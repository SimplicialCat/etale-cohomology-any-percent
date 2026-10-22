// audit-exception: 作者 R3 意见：把求值映射明确写作 $e_n$，只补出符号，数学内容未变。
#import "void-import.typ": *

本附录证明 Brown 可表示性定理：它给出三角函子 $D(cal(A)) -> cal(D)$ 有右伴随的形式判别法。定理的陈述是： 

- 设 $cal(A)$ 是 Grothendieck Abel 范畴。则任何保持任意直和的三角函子 $D(cal(A)) -> cal(D)$ 都必有三角右伴随。 

证明分两步：先用 Gabriel–Popescu 定理归约到模范畴 $AMod(R)$，再用 Brown 可表示性定理的紧情形完成剩下的论证。 

#theorem(name: <gabriel-popescu>)[
  (Gabriel–Popescu 定理) 设 $cal(A)$ 是 Grothendieck Abel 范畴。则存在非交换环 $R$ 与函子： 
  $
    Q: AMod(R) arrows.rl cal(A): G
  $
  其中 $Q$ 是 $G$ 的左伴随，$G$ 全忠实，$Q$ 正合。 
]
#proof[
  设 $U in cal(A)$ 是生成元，$R = End_(cal(A)) (U)$ 是它的自同态环。令： 
  $
    G: cal(A) -> AMod(R), A |-> Hom_(cal(A)) (U, A)
  $
  此时每个 $G(A) = Hom_(cal(A)) (U, A)$ 都通过复合成为右 $R$-模。另一方面，要定义 $Q$，注意对任意 $M in AMod(R)$ 都有典范自由消解： 
  $
    R^(oplus K(M)) ->^A R^(oplus M) -> M -> 0
  $
  其中 $K(M) = ker(R^(oplus M) -> M)$。设 $A$ 由矩阵 $display(mat(r_(m,k))_(k in K(M),m in M))$ 表示，其中 $r_(m,k) in R = End_(cal(A)) (U)$ 是 $U$ 的自同态。于是 $A$ 诱导出态射： 
  $
    A_U: U^(oplus K(M)) -> U^(oplus M), (u_k) |-> (sum_(k in K(M)) r_(m,k)(u_k))_m
  $
  （注：$cal(A)$ 是一般的 Abel 范畴，$U$ 是个抽象的对象，所以上面那个用 $U$ 的元素写出的公式其实没有意义。话虽如此，$A_U$ 仍是由各个 $r_(m,k): U -> U$ 在相应直和项上诱导出的唯一态射。）

  现在定义： 
  $
    Q: AMod(R) -> cal(A), M |-> coker(A_U\: U^(oplus K(M)) -> U^(oplus M))
  $
  $Q$ 是函子，因为 $M$ 的自由消解是函子性的。现在有： 
  $
    Hom_(cal(A)) (Q(M), A) &= Hom_(cal(A)) (coker(A_U\: U^(oplus K(M)) -> U^(oplus M)), A) \
    &= ker(Hom_(cal(A)) (U^(oplus M), A) -> Hom_(cal(A)) (U^(oplus K(M)), A)) \
    // &= ker(product_M Hom(U, A) -> product_(K(M)) Hom(U, A)) \
    &= ker(G(A)^M -> G(A)^(K(M))) \
    &= ker(Hom_R (R^(oplus M), G(A)) -> Hom_R (R^(oplus K(M)), G(A)))\
    &= Hom_R (coker(R^(oplus K(M)) -> R^(oplus M)), G(A)) \
    &= Hom_R (M, G(A))
  $
  因此 $Q$ 是 $G$ 的左伴随。作为左伴随，$Q$ 自动右正合。 

  - 注意：#h(1fr)
    $
      Hom_(cal(A)) (U^(oplus I), A) = G(A)^I = Hom_R (R^(oplus I), G(A))
    $
    于是 $Q(R^(oplus I)) = U^(oplus I)$。 

  - 我们断言：若 $i: M arrow.hook G(A)$ 是单射，则由伴随诱导的态射 $tilde(i): Q(M) arrow A$ 也是单射。 

    任给映射 $g: R^n -> M$，把 $Q$ 作用于它，便得到映射 $Q(g): U^n -> Q(M)$。而任何映射 $alpha: U -> U^n$ 都由 $Hom_(cal(A)) (U, U) = R$ 中的 $n$ 个元素确定，因此由函子性，它来自某个 $a: R -> R^n$，即 $alpha = Q(a)$。我们断言： 
    $
      tilde(i) compose Q(g) compose Q(a) = 0 <==> Q(g) compose Q(a) = 0
    $
    只需证明 $(==>)$。若 $tilde(i) compose Q(g) compose Q(a) = 0$，则由伴随性，$i compose g compose a: R -> M$ 为零。$i$ 是单射，故 $g compose a = 0$，从而 $Q(g) compose Q(a) = 0$。于是对任意映射 $alpha: U -> U^n$，都有 $tilde(i) compose Q(g) compose alpha = 0 <==> Q(g) compose alpha = 0$。也就是说， 
    $
      Hom_(cal(A)) (U, ker(Q(g))) -> Hom_(cal(A)) (U, ker(tilde(i) compose Q(g)))
    $
    是同构。$U$ 是生成元，故 $ker(Q(g)) = ker(tilde(i) compose Q(g))$。 

    现在取任意自由消解 $h: R^(oplus I) -> M$。上面的论证说明：对任意有限子集 $I' subset I$，$h_(I'): R^(oplus I')$ 满足： 
    $
      ker(Q(h_(I'))) = ker(tilde(i) compose Q(h_(I')))
    $
    对所有有限 $I' subset I$ 取正向极限，并用 (Ab5)，得： 
    $
      ker(Q(h)) = ker(tilde(i) compose Q(h))
    $
    由于 $Q(h)$ 是满射（$Q$ 右正合），这说明 $tilde(i)$ 是单射。 

  现在把上述断言用于 $id_(G(A))$，便知单位 $eta_A: Q G (A) -> A$ 总是单射。另一方面，任意映射 $U = Q(R) -> A$ 都可看作 $G(A)$ 的元素，并分解为 $U = Q(R) -> Q G(A) -> A$，从而穿过 $eta_A$。于是求值映射 $oplus.big_(phi in Hom_(cal(A)) (U,A)) U -> A$ 也穿过 $eta_A$；而求值映射是满射，故 $eta_A$ 是满射。因此余单位 $eta: Q G -> id$ 是自然同构，等价地说，$G$ 全忠实。 

  最后证明 $Q$ 正合。它已经右正合，故只需证明它保持单射。 

  - 先设有一个包含 $K arrow.hook R^(oplus I) = G(U^(oplus I))$。上面的断言表明 $Q(K) -> Q(R^(oplus I)) = U^(oplus I)$ 是单射。 

  - 对 $AMod(R)$ 中一般的包含 $A arrow.hook B$，取自由消解 $P -> B$，并令： 
    $
      L = ker(P -> B), K = A times_B P
    $
    于是 $L subset K subset P$，且有等同 $A = K\/L, B = P\/L$。由 $Q$ 右正合， 
    $
      Q(A) = Q(K)\/Q(L), Q(B) = Q(P)\/Q(L)
    $
    由上一项，既然 $P$ 是自由的，便有 $Q(K) -> Q(P)$ 是单射。于是 $Q(A) -> Q(B)$ 是单射。 

  证毕。 
]

#corollary(name: <gabriel-popescu-derived>)[
  设 $cal(A)$ 是 Grothendieck Abel 范畴。@gabriel-popescu 中定义的函子 $Q: AMod(R) arrows.rl cal(A): G$ 过渡到无界导出范畴： 
  $
    Q: D(R) arrows.rl D(cal(A)): R G
  $
  使得 $Q$ 是 $R G$ 的左伴随，且 $R G$ 全忠实。 
]
#proof[
  $cal(A)$ 是 Grothendieck Abel 范畴，有足够多的内射对象。其余部分由 @gabriel-popescu 形式推出。 
]

下面给出紧情形的 Brown 可表示性定理，作为整个论证的跳板。 

#notation(name: <compact-objects-and-generators>)[
  在三角范畴 $cal(D)$ 中，若 $Hom_(cal(D)) (G, -): cal(D) -> cAb$ 与任意直和交换，则称对象 $G in cal(D)$ 为*紧的*。 

  一族紧对象 $cal(G) subset cal(D)$ 若满足下述条件，则称 $cal(G)$ *生成* $cal(D)$： 

  - 对任意 $X in cal(D)$，若对所有 $G in cal(G), n in ZZ$ 都有 #h(1fr)
    $
      Hom_(cal(D)) (G[n], X) = 0
    $
    则 $X = 0$。 
]

#construction(name: <telescoping-construction>)[
  （望远镜构造 (telescoping construction)）设三角范畴 $cal(D)$ 具有任意直和，并设有一串映射 $X_0 ->^(u_0) X_1 ->^(u_1) dots.c$。 

  令 $S = oplus.big_(n>=0) X_n$，包含映射为 $i_n: X_n -> S$；再定义映射 $sigma: S -> S$：在每个直和项上取映射 $X_n -> X_(n+1)$，即 $u_n$。换言之， 
  $
    sigma compose i_n = i_(n+1) compose u_n
  $
  作特殊三角： 
  $
    S -->^(1-sigma) S -->^q X_oo ->^(+1)
  $
  并令 $j_n = q compose i_n: X_n -> X_oo$。由于 $q compose (1 - sigma) = 0$，有： 
  $
    j_n = q compose i_n = q compose sigma compose i_n = q compose i_(n+1) compose u_n = j_(n+1) compose u_n
  $
  注意 $X_oo$ 的选取并不典范（即在唯一同构意义下唯一），它只是 $1-sigma: S -> S$ 的任意一个锥。它具有下述性质： 

  - 对任意（共变的）上同调函子 $F: cal(D) -> cal(A)$（$cal(A)$ 是某个 Abel 范畴），只要它保持直和，态射 $j_n: X_n -> X_oo$ 就诱导出同构：#h(1fr)
    $
      dirlim_(n>=0) F(X_n) cong F(X_oo)
    $
    事实上，把 $F(-)$ 作用于 $S -->^(1-sigma) S -->^q X_oo ->^(+1)$，并利用 $F$ 保持直和，即得长正合列： 
    $
      & oplus.big_(n>=0) F(X_n) ->^D oplus.big_(n>=0) F(X_n) -> F(X_oo) -> oplus.big_(n>=0) F(X_n [1]) ->^(D') oplus.big_(n>=0) F(X_n [1])
    $
    其中： 
    $
      D: oplus.big_(n>=0) F(X_n) -> oplus.big_(n>=0) F(X_n), (a_n)_n |-> (a_n - F(u_(n-1)) a_(n-1))_n \

      D': oplus.big_(n>=0) F(X_n [1]) -> oplus.big_(n>=0) F(X_n [1]), (a_n)_n |-> (a_n - F(u_(n-1) [1]) compose a_(n-1))_n
    $
    两个映射都是单射。事实上，若 $(a_n)_n in ker(D)$，则： 
    $
      a_0 = 0 \
      a_n = F(u_(n-1)) a_(n-1), forall n>=1
    $
    归纳可知所有 $a_n = 0$。$D'$ 同理。既然 $D'$ 是单射，就有等同： 
    $
      F(X_oo) cong coker(D\: oplus.big_(n>=0) F(X_n) -> oplus.big_(n>=0) F(X_n))
    $
    不过，按 $D$ 的定义，这个余核正是 $dirlim_(n>=0) F(X_n)$。 

    特别地，对紧对象 $G in cal(D)$，有 $Hom_(cal(D)) (G, X_oo) = dirlim_(n>=0) Hom_(cal(D)) (G, X_n)$。 

  - 对偶的陈述是：对任意反变上同调函子 $H: cal(D)^opp -> cal(A)$，若它把直和送成直积，则 
    $
      H(X_oo) -> invlim_(n>=0) H(X_n) 
    $
    是满射。 

    事实上，把 $H$ 作用于 $S -->^(1-sigma) S -->^q X_oo ->^(+1)$，即得下述映射的正合性： 
    $
      H(X_oo) -> product_(n>=0) H(X_n) ->^D product_(n>=0) H(X_n)
    $
    其中： 
    $
      D: product_(n>=0) H(X_n) -> product_(n>=0) H(X_n), (a_n)_n |-> (a_n - H(u_(n+1)) a_(n+1))_n
    $
    按定义 $invlim_(n>=0) H(X_n) = ker(D)$，故有满射 $H(X_oo) -> invlim_(n>=0) H(X_n)$。 
]

#lemma(name: <cpct-generation-of-triangulated-cat>)[
  设三角范畴 $cal(D)$ 具有任意直和，且有一族生成 $cal(D)$ 的紧对象 $cal(G)$。则 $cal(D)$ 中含 $cal(G)$ 且对任意直和封闭的三角子范畴 $cal(E)$ 必定是 $cal(D)$ 本身。 
]
#proof[
  不妨把 $cal(G)$ 换成由其中所有元素的平移构成的集合，并假设它对平移封闭。 
  
  我们归纳地构造一串映射 $P_0 ->^(u_0) P_1 -> dots.c$。 
  
  - 对任意 $X in cal(D)$，令：#h(1fr)
    $
      P_0 = oplus.big_(G in cal(G) \ h: G -> X) G
    $
    求值映射为 $p_0: P_0 -> X$。 

  - 假设 $p_n: P_n -> X$ 已定义。令：
    $
      Q_n = oplus.big_(G in cal(G) \ h: G -> P_n, p_n compose h = 0) G
    $
    其中求值映射为 $e_n: Q_n -> P_n$（按定义有 $p_n compose e_n = 0$）。把 $e_n$ 补成特殊三角： 
    $
      Q_n -->^(e_n) P_n -->^(u_n) P_(n+1) ->^(+1)
    $

    注意 $Hom_(cal(D)) (P_(n+1), X) -> Hom_(cal(D)) (P_n, X) -> Hom_(cal(D)) (Q_n, X)$ 正合，再加上 $u_n compose e_n = 0$，便得到提升 $p_(n+1): P_(n+1) -> X$，使得 $p_(n+1) compose u_n = p_n$。 

  现在对 $P_0 ->^(u_0) P_1 ->^(u_1) -> dots.c$ 作望远镜 $S_P = oplus.big_(n>=0) P_n -->^(1-sigma) S_P -->^q P_oo$，并令 $j_n: P_n -> P_oo$。由于 $Hom_(cal(D)) (-, X)$ 是把直和送成直积的反变上同调函子， 
  $
    Hom_(cal(D)) (P_oo, X) -> invlim_(n>=0) Hom_(cal(D)) (P_n, X)
  $
  是满射。于是存在 $p_oo: P_oo -> X$，使得 $p_n = p_oo compose j_n$。 

  我们断言，对所有 $G in cal(G)$， 
  $
    Hom_(cal(D)) (G, p_oo): Hom_(cal(D)) (G, P_oo) -> Hom_(cal(D)) (G, X)
  $
  是双射。它是满射，因为它穿过按定义即满射的 $Hom_(cal(D)) (G, P_0) -> Hom_(cal(D)) (G, X)$ 分解。再证它是单射：$G$ 紧，故 $Hom_(cal(D)) (G, P_oo) cong dirlim_(n>=0) Hom_(cal(D)) (G, P_n)$，于是只需证明： 
  $
    dirlim_(n>=0) Hom_(cal(D)) (G, P_n) -> Hom_(cal(D)) (G, X)
  $
  是单射。事实上，若 $h in Hom_(cal(D)) (G, P_n)$ 落在这个映射的核中，则 $p_n compose h = 0$，于是 $h$ 对应 $Q_n$ 的一个直和项。进而 $h: G -> P_n$ 穿过 $e_n: Q_n -> P_n$ 分解，故 $u_n compose h = 0$。也就是说，$h$ 在正向极限 $dirlim_(n>=0) Hom_(cal(D)) (G, P_n)$ 的下一层变成 $0$。单射性由此得证。 

  既然已证 $Hom_(cal(D)) (G, P_oo) -> Hom_(cal(D)) (G, X)$ 是同构，就可以作锥 $P_oo -->^(p_oo) X -> C ->^(+1)$。于是： 
  $
    Hom_(cal(D)) (G, C) = 0
  $
  对所有 $G in cal(G)$ 成立，从而 $C = 0$。所以 $p_oo$ 是同构。剩下要证 $P_oo in cal(E)$。 

  事实上： 

  - $P_0 in cal(E)$，且每个 $Q_n in cal(E)$ 都是 $cal(G)$ 中对象的直和，而 $cal(E)$ 含 $cal(G)$ 且对任意直和封闭。 

  - 再由特殊三角 $Q_n -> P_n -> P_(n+1) ->^(+1)$ 归纳可知每个 $P_n in cal(E)$。 

  - 于是由 $cal(E)$ 对直和的封闭性，$S_P = oplus.big_(n>=0) P_n in cal(E)$；又由三角 $S_P -->^(1-sigma) S_P -> P_oo ->^(+1)$，得 $P_oo in cal(E)$。 

  证毕。 
]

#lemma(name: <ptwise-brown-representability-cpct-case>)[
  (紧情形的逐点 Brown 可表示性) 设三角范畴 $cal(D)$ 具有任意直和，且有一族生成 $cal(D)$ 的紧对象 $cal(G)$。设 $H: cal(D)^opp -> cAb$ 是把直和送成直积的反变上同调函子。则 $H$ 可表示。 
]
#proof[
  不妨把 $cal(G)$ 换成它在平移下的闭包，并假设 $cal(G)$ 对平移封闭。 

  元素 $a in H(X)$ 定义了自然变换： 
  $
    theta_Y^a: Hom_(cal(D)) (Y, X) -> H(Y), f |-> H(f) a
  $
  我们要构造 $X in cal(D)$ 与 $a in H(X)$，使得这个 $theta^a$ 是自然同构。取： 
  $
    X_0 = oplus.big_(G in cal(G) \ x in H(G)) G
  $
  由于 $H$ 把直和送成直积，$H(X_0) = product_(G in cal(G) \ x in H(G)) H(G)$，故可取 $a_0 = (x)_(G,x) in H(X_0)$。于是对任意 $G in cal(G)$，映射 
  $
    theta_G^(a_0): Hom_(cal(D))(G, X_0) -> H(G)
  $
  按定义是满射：每个元素 $x in H(G)$ 都是把 $a_0$ 投影到对应 $(G,x)$ 的因子上得到的。 

  假设已构造出 $X_n in cal(D), a_n in H(X_n)$。取： 
  $
    K_n = oplus.big_(G in cal(G) \ k: G -> X_n, H(k)a_n = 0) G
  $
  并令 $r_n: K_n -> X_n$ 为这样的映射：在以 $k$ 为指标的那个直和项上，它恰好是 $k: G -> X_n$。按定义，$H(r_n) a_n = 0 in H(K_n)$，因为： 
  $
    H(K_n) = product_(G in cal(G) \ k:G -> X_n, H(k)a_n = 0) H(G)
  $
  且 $H(r_n) a_n = (H(k)a_n)_(G,k) = 0$。作特殊三角： 
  $
    K_n -->^(r_n) X_n -->^(u_n) X_(n+1) ->^(+1)
  $
  由于 $H$ 是上同调函子，$H(X_(n+1)) -> H(X_n) -> H(K_n)$ 正合。又 $H(r_n) a_n = 0$，故存在 $a_(n+1) in H(X_(n+1))$，使得 $a_n = H(u_n) a_(n+1)$。 
  
  现在对 $X_0 ->^(u_0) X_1 ->^(u_1) dots.c$ 作望远镜 $X_oo$，映射记为 $j_n: X_n -> X_oo$。由于 $H$ 把直和送成直积， 
  $
    H(X_oo) -> invlim_(n>=0) H(X_n)
  $
  是满射。于是存在 $a_oo in H(X_oo)$，使得对所有 $n$ 都有 $a_n = H(j_n) a_oo$。我们断言： 
  $
    theta^(a_oo)_G: Hom_(cal(D)) (G, X_oo) -> H(G)
  $
  是双射。 

  - 它是满射，因为它穿过 $theta^(a_0)_G: Hom_(cal(D)) (G, X_0) -> H(G)$ 分解，而这个映射如我们所证是满射。 

  - 它是单射：假设 $f in Hom_(cal(D)) (G, X_oo)$ 满足 $H(f)a_oo = 0$。$G$ 紧，故 
    $
      Hom_(cal(D)) (G, X_oo) = dirlim_(n>=0) Hom_(cal(D)) (G, X_n)
    $
    于是存在 $f_n: G -> X_n$，使得 $f = j_n compose f_n$。因此， 
    $
      H(f_n) a_n = H(f_n) H(j_n) a_oo = 0
    $
  于是 $(G, f_n)$ 对应 $K_n$ 中的一个直和项。所以 $f_n: G -> X_n$ 穿过 $r_n: K_n -> X_n$ 分解，从而 $u_n compose f_n = 0$。故 
    $
      f = j_n compose f_n = j_(n+1) compose u_n compose f_n = 0
    $
    单射性得证。 

  现在设 $cal(P)$ 是 $cal(D)$ 的满子范畴，其对象为： 
  $
    cal(P) = {Y in cal(D): theta^(a_oo)_Y: Hom_(cal(D)) (Y, X_oo) -> H(Y) #[是同构]}
  $
  由于 $Hom_(cal(D)) (-, X_oo)$ 与 $H$ 都是三角函子，$cal(P)$ 对平移与特殊三角封闭。又因 $Hom_(cal(D)) (-, X_oo)$ 与 $H$ 都把直和送成直积，$cal(P)$ 对任意直和封闭。最后，如我们已经证明的，$cal(G) subset cal(P)$。于是由 @cpct-generation-of-triangulated-cat，$cal(P) = cal(D)$。 

  因此 $theta^(a_oo)$ 给出自然同构 $H cong Hom_(cal(D)) (-, X_oo)$，从而用 $X_oo in cal(D)$ 表示 $H$。 
]

#lemma(name: <ptwise-brown-representability>)[
  (逐点 Brown 可表示性) 设 $cal(A)$ 是 Grothendieck Abel 范畴。设 $H: D(cal(A))^opp -> cAb$ 是把直和送成直积的反变上同调函子。则 $H$ 可表示。 
]
#proof[
  由 @gabriel-popescu-derived，可取非交换环 $R$ 与一对三角伴随函子： 
  $
    Q: D(R) -> D(cal(A)): G
  $
  其中 $G$ 全忠实（即余单位 $eta: Q G -> id$ 是自然同构）。 

  考虑函子 $H compose Q: D(R)^opp -> cAb$。$Q$ 是左伴随，故保持直和；于是 $H compose Q$ 也把直和送成直积。此外，三角范畴 $D(R)$ 由紧对象 ${R[n]}_(n in ZZ)$ 生成。故由 @ptwise-brown-representability-cpct-case，$H compose Q$ 可表示，即存在对象 $L in D(R)$ 与自然同构： 
  $
    H(Q(C)) cong Hom_(D(R)) (C, L)
  $
  取单位映射 $u_L: L -> G Q(L)$，作锥： 
  $
    M -> L ->^(u_L) G Q(L) ->^(+1)
  $
  注意由伴随恒等式，$Q(u_L): Q(L) -> Q G Q(L)$ 是同构。于是把 $Q$ 作用于上述特殊三角，可知 $Q(M) = 0$，从而 $Hom_(D(R)) (M, L) cong H(Q(M)) = 0$。因此把 $Hom_(D(R)) (-, L)$ 作用于上述特殊三角，得到满射： 
  $
    Hom_(D(R)) (G Q(L), L) ->> Hom_(D(R)) (L, L)
  $
  取在该态射下映为 $id_L$ 的 $r_L: G Q(L) -> L$，便知 $r_L compose u_L = id_L$，即 $r_L$ 是 $L$ 的回缩。 

  由 $G$ 全忠实，我们得到一个回缩： 
  $
    H(A) cong H(Q G (A)) cong Hom_(D(R)) (G(A), L) \
    ->^(u_L compose -) Hom_(D(R)) (G(A), G Q(L)) cong Hom_(D(cal(A))) (A, Q(L))
  $
  现在 $u_L compose -$ 有左逆 $r_L compose -$。因此 $H$ 是可表示函子 $Hom_(D(cal(A))) (-, Q(L))$ 的直和项。 

  - 注意 $D(cal(A))$ 是幂等完备 (idempotent complete) 的，也就是说，$D(cal(A))$ 中每个幂等态射 $e: X -> X$ 都分裂为 $e: X ->^f Y ->^g X$，其中 $f compose g = id_Y$。

    事实上，对链 $X ->^e X ->^e -> dots.c$ 作望远镜 $Y$，它是一个锥： 
    $
      oplus.big_(n>=0) X ->^(1-sigma) oplus.big_(n>=0) X ->^q Y ->^(+1)
    $
    其中 $sigma((x_n)_n) = (e x_(n-1))_n$。 

    令 $ell: oplus.big_(n>=0) X -> oplus.big_(n>=0) X, (x_n)_n |-> (x_n - sum_(k>=n) e x_k)_n$。则： 
    $
      ell(1-sigma)((x_n)_n) = ell((x_n - e x_(n-1))_n) = ((x_n - e x_(n-1)) - sum_(k>=n) (e x_k - e x_(k-1)))_n = (x_n)_n
    $
    于是 $ell$ 是 $1 - sigma$ 的左逆。既然 $1 - sigma$ 有左逆，上面的三角就是分裂三角，即 $+1$ 映射 $Y -> oplus.big_(n>=0) X[1]$ 为零，且 $q$ 有右逆。于是得到短正合列： 
    $
      0 -> Hom_(D(cal(A))) (Y, X) -> product_(n>=0) Hom_(D(cal(A))) (X, X) -> product_(n>=0) Hom_(D(cal(A))) (X, X) -> 0
    $
    令 $r: oplus.big_(n>=0) X -> X$ 为 $(x_n)_n |-> sum_(n>=0) e x_n$。则 $r = r compose sigma$，故 $r compose (1-sigma) = 0$。于是存在 $g: Y -> X$，使得 $g compose q = r$。 

    设 $i_n: X -> oplus.big_(n>=0) X$ 是到第 $n$ 个直和项的包含。再令 $f = q compose i_0: X -> Y$。此时： 
    $
      g compose f = g compose q compose i_0 = r compose i_0 = e
    $
    以及： 
    $
      f compose g compose q = f compose r
    $
    - 由 $q = q compose sigma$，在等式两边右侧与 $i_n$ 复合，得 $q compose i_n = q compose i_(n+1) compose e$。再在右侧与 $e$ 复合，并利用幂等性，得 $q compose i_n compose e = q compose i_(n+1) compose e = q compose i_n$，于是： 
      $
        q compose i_n = q compose i_(n+1)
      $
      从而对所有 $n$ 都有 $f = q compose i_n$，且 $f = f compose e$。现在： 
      $
        f compose r compose i_n = f compose e = f = q compose i_n
      $
      对所有 $n$ 成立，故 $f compose r = q$
    于是 $f compose g compose q = q$。$q$ 有右逆，故 $f compose g = id$。这样就把幂等态射 $e$ 分裂了。

  既然 $H$ 是 $Hom_(D(cal(A))) (-, Q(L))$ 的直和项，它就对应 $Q(L)$ 的一个幂等态射，该幂等态射分解为 $Q(L) ->^f T ->^g Q(L)$，其中 $f compose g = id$。于是 $T$ 表示 $H$。 
]

#theorem(name: <brown-representability>)[
  (Brown 可表示性) 设 $cal(A)$ 是 Grothendieck Abel 范畴。则任何保持任意直和的三角函子 $D(cal(A)) -> cal(D)$ 都必有三角右伴随。 
]
#proof[
  设 $F: D(cal(A)) -> cal(D)$ 是保持任意直和的三角函子。对每个 $X in cal(D)$，函子 $Hom_(cal(D)) (F(-), X)$ 把直和送成直积。由 @ptwise-brown-representability，每个 $Hom_(cal(D)) (F(-), X)$ 都可表示。于是 $F$ 有加性右伴随： 
  $
    G: cal(D) -> D(cal(A))
  $
  剩下要证 $G$ 是三角函子。由伴随性，$G$ 保持所有平移。 

  设 $A ->^f B ->^g C ->^u_(+1)$ 是 $cal(D)$ 中的特殊三角，并作特殊三角： 
  $
    G(A) ->^(G(f)) G(B) -> X ->^(+1)
  $
  此时 $F G(A) -> F G(B) -> F(X) ->^(+1)$ 是特殊三角。于是由三角公理，存在映射 $phi: F(X) -> C$ 使下图交换： 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJGIEcoQSkiXSxbMCwxLCJBIl0sWzEsMCwiRiBHKEIpIl0sWzIsMCwiRihYKSJdLFszLDAsIkYgRyhBKVsxXSJdLFsxLDEsIkIiXSxbMiwxLCJDIl0sWzMsMSwiQVsxXSJdLFszLDRdLFswLDJdLFsyLDNdLFsxLDUsImYiLDJdLFs1LDYsImciLDJdLFs2LDcsInUiLDJdLFswLDEsImV0YV9BIiwyXSxbMiw1LCJldGFfQiJdLFszLDYsInBoaSJdLFs0LDcsImV0YV9BIFsxXSJdXQ==
  #align(center, diagram({
    node((0, 0), [$F G(A)$])
    node((0, 1), [$A$])
    node((1, 0), [$F G(B)$])
    node((2, 0), [$F(X)$])
    node((3, 0), [$F G(A)[1]$])
    node((1, 1), [$B$])
    node((2, 1), [$C$])
    node((3, 1), [$A[1]$])
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (1, 0), "->")
    edge((1, 0), (2, 0), "->")
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
    edge((1, 1), (2, 1), [$g$], label-side: right, "->")
    edge((2, 1), (3, 1), [$u$], label-side: right, "->")
    edge((0, 0), (0, 1), [$eta_A$], label-side: right, "->")
    edge((1, 0), (1, 1), [$eta_B$], label-side: left, "->")
    edge((2, 0), (2, 1), [$phi$], label-side: left, "->")
    edge((3, 0), (3, 1), [$eta_A [1]$], label-side: left, "->")
  }))
  由伴随性，得到交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJHKEEpIl0sWzAsMSwiRyhBKSJdLFsxLDAsIkcoQikiXSxbMiwwLCJYIl0sWzMsMCwiRyhBKVsxXSJdLFsxLDEsIkcoQikiXSxbMiwxLCJHKEMpIl0sWzMsMSwiRyhBWzFdKSJdLFszLDRdLFswLDIsIkcoZikiXSxbMiwzXSxbMSw1LCJHKGYpIiwyXSxbNSw2LCJHKGcpIiwyXSxbNiw3LCJ1IiwyXSxbMiw1LCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzMsNiwicHNpIl0sWzQsNywidGlsZGUiXSxbMCwxLCIiLDIseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV1d
  #align(center, diagram({
    node((0, 0), [$G(A)$])
    node((0, 1), [$G(A)$])
    node((1, 0), [$G(B)$])
    node((2, 0), [$X$])
    node((3, 0), [$G(A)[1]$])
    node((1, 1), [$G(B)$])
    node((2, 1), [$G(C)$])
    node((3, 1), [$G(A[1])$])
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (1, 0), [$G(f)$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((0, 1), (1, 1), [$G(f)$], label-side: right, "->")
    edge((1, 1), (2, 1), [$G(g)$], label-side: right, "->")
    edge((2, 1), (3, 1), [$u$], label-side: right, "->")
    edge((1, 0), (1, 1), "=")
    edge((2, 0), (2, 1), [$psi$], label-side: left, "->")
    edge((3, 0), (3, 1), [$tilde$], label-side: left, "->")
    edge((0, 0), (0, 1), "=")
  }))
  按照由伴随得到的同构 $G(A)[1] cong G(A[1])$ 的构造方式，上面这个交换图表便过渡为三角之间的态射： 
  #align(center, diagram({
    node((0, 0), [$G(A)$])
    node((0, 1), [$G(A)$])
    node((1, 0), [$G(B)$])
    node((2, 0), [$X$])
    node((3, 0), [$G(A)[1]$])
    node((1, 1), [$G(B)$])
    node((2, 1), [$G(C)$])
    node((3, 1), [$G(A[1])$])
    edge((2, 0), (3, 0), "->")
    edge((0, 0), (1, 0), [$G(f)$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((0, 1), (1, 1), [$G(f)$], label-side: right, "->")
    edge((1, 1), (2, 1), [$G(g)$], label-side: right, "->")
    edge((2, 1), (3, 1), [$u$], label-side: right, "->")
    edge((1, 0), (1, 1), "=")
    edge((2, 0), (2, 1), [$psi$], label-side: left, "->")
    edge((3, 0), (3, 1), label-side: left, "=")
    edge((0, 0), (0, 1), "=")
  }))
  对任意 $W in D(cal(A))$，对上述三角作用 $Hom_(D(cal(A))) (W, -)$，再用五引理，便知 $Hom_(D(cal(A))) (W, X) -> Hom_(D(cal(A))) (W, G(C))$ 是同构。由 Yoneda 引理，$psi$ 是同构。于是 $G(A) -> G(B) -> G(C) ->^(+1)$ 同构于一个特殊三角，从而是特殊三角。 
]
