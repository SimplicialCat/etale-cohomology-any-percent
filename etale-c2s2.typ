// audit-exception: 作者英文修正同步：原文“理想含于 frak(m)_(x_i)”系笔误；中文删除该错误断言，并补出核为 (frak(p),T)。数学内容按英文修正，未改其他公式。
#import "void-import.typ": *

== 平展态射的局部结构

本节给出平展态射与光滑态射的显式 (Zariski) 局部描述。

本节的论证大多取自 Stacks Project。

#definition(name: <defn-standard-etale-morphism>)[
  如下形式的态射称为*标准平展态射* (standard étale morphism)：
  $
    Spec((A[T]_(h(T)))/((g(T)))) -> Spec(A)
  $
  其中 $g(T), h(T) in A[T]$，$g(T)$ 首一，且 $(g'(T), g(T)) = (1) subset A[T]_(h(T))$。这个态射的相对微分层为：
  $
    Omega_((A[T]_(h(T))\/g(T))\/A) cong (A[T]_(h(T)) d T)/((g(T), g'(T))) = 0
  $
  另外，由于 $g(T)$ 首一，$A[T]_(h(T))\/g(T)$ 是有限自由 $A$-代数的局部化，从而在 $A$ 上平坦。因此标准平展态射必定平展。
]

#theorem(name: <local-struct-of-etale-morphisms>)[
  （平展态射的局部结构） 设 $f: X -> Y$ 是在 $x$ 处平展的态射，$y = f(x)$。则存在仿射开集 $x in U = Spec(B) subset X$ 与 $y in V = Spec(A) subset Y$，使得 $f(U) subset V$，且 $f: Spec(B) -> Spec(A)$ 同构于某个标准平展态射。
]
#proof[
  平展性对底与源都是局部的，故把 $X, Y$ 在 $x, y$ 附近适当缩小，不妨设 $X = Spec(B), Y = Spec(A)$ 都是仿射的。平展性对源也是局部的，因此再适当缩小 $X, Y$，不妨设 $f$ 平展。

  现在 $f$ 是有限展示的，故由 @absolute-noetherian-approx、@passage-to-limit-of-morphisms 与 @passage-to-limit-of-properties (3d)，不妨设 $f$ 由平展态射 $f_0: X_0 -> Y_0$ 经基变换得到，其中 $X_0, Y_0$ 是 $ZZ$ 上有限型的仿射概形。标准平展态射经仿射态射做基变换，仍然标准平展。于是可以把 $f$ 换成 $f_0$，并假定 $X, Y$ 也是 $ZZ$ 上有限型的，特别地是 Noether 的。

  第一步。适当选取函数 $b in B$，构造浸入 $X -> AA^1_Y$。
  
  #proof[
    平展态射拟有限，故由 Zariski 主定理，可把 $f$ 分解为：
    $
      X = Spec(B) ->^j Z = Spec(C) ->^(ol(f)) Y = Spec(A)
    $
    其中 $j$ 是开浸入，$ol(f)$ 有限。把 $f$ 换成 $ol(f)$，不妨设 $f$ 有限且在 $x$ 处平展（同时放弃 $f$ 整体平展这一假设）。设 $x in X, y in Y$ 分别对应素理想 $frak(q) subset B, frak(p) subset A$。现在看纤维 $X_y$，它是下列环的谱：
    $
      B otimes_A k(y) = product_(i=1)^m T_i
    $
    这里 $B otimes_A k(y)$ 在 $k(y)$ 上有限，因而是 Artin 环，并且是若干 Artin 局部环 $T_i$ 的积。纤维 $X_y$ 中每个点对应一个直积项，故设 $x in X_y$ 对应直积项 $T_1$。记 $X_y = {x = x_1, x_2, dots.c, x_m}$。
    
    由于 $f$ 在 $x$ 处平展，$T_1 = k(x)$ 是域，并且是 $k(y)$ 的有限可分扩张。取 $k(x)\/k(y)$ 的一个本原元 $alpha != 0$，考虑元素：
    $
      beta = (underbrace(alpha, in T_1 = k(x)), underbrace(0, in T_2), dots.c, underbrace(0, in T_m)) in B otimes_A k(y) = product_(i=1)^m T_i
    $
    由 $B otimes_A k(y) = B_(frak(p))\/frak(p) B_(frak(p))$ 可知，存在 $b in B_(frak(p))$ 使 $beta = b mod frak(p) B_(frak(p))$。我们把分母清掉，使提升落在 $B$ 中：将 $beta$ 乘以 $A - frak(p)$ 中一个适当的元素。这相当于将 $alpha$ 乘以 $k(y)$ 中的某个非零元素，不影响 $0 != alpha$ 及 $k(x) = k(y)(alpha)$ 这两个事实。于是可将 $beta$ 提升为 $b in B$，得到分解：
    $
      A -> A[T] -->^("ev"_b) B
    $
    也就是 $f$ 的一个分解 $Spec(B) ->^h Spec(A[T]) ->^p Spec(A)$。取理想 $I = ker("ev"_b) subset A[T]$ 与子环 $A[b] = im("ev"_b) subset B$。实际上我们有分解：
    $
      Spec(B) -> Spec(A[b]) cong Spec(A[T]\/I) -> Spec(A[T]) -> Spec(A)
    $
    这里 $I$ 含有一个首一多项式，因为 $B$ 在 $A$ 上有限。

    我们断言 $Spec(B) -> Spec(A[T]\/I)$ 在 $x$ 附近是开浸入。令 $D = A[b] cong A[T]\/I$，并将 $x = frak(q) in Spec(B)$ 的像记为 $frak(r) in Spec(D)$（也把该像看作含 $I$ 的素理想 $frak(r) subset A[T]$）。$B$ 在 $A$ 上有限，故在 $D$ 上有限。
    
    只需验证 $B_(frak(q)) cong D_(frak(r))$。现在：

    - 注意 $frak(q) in Spec(B)$ 是唯一位于 $frak(r) in Spec(D)$ 之上的素理想。事实上，任何位于 $frak(r)$ 之上的素理想 $x' = frak(q)' in Spec(B)$ 都必定位于 $y = frak(p) in Spec(A)$ 之上，从而对应 $X_y$ 中的一个点。这个点 $x' = x_i$ 对应 $B otimes_A k(y) = product_(i=1)^m T_i$ 中的一个直积项 $T_i$。若 $i >= 2$，则 $x_i$ 位于素理想之上：
      $
        ker(A[T] -->^("ev"_b) B\/frak(m)_(x_i) B) in Spec(A[T])
      $
      由于 $b |-> 0 in T_i$，这个理想含有 $T$。另一方面，$x_i$ 位于 $y = frak(p)$ 之上，故 $ker(A -> B\/frak(m)_(x_i) B)$ 就是 $frak(p)$。因此，这个核正是 $(frak(p), T)$。总之，$x_2, dots.c, x_m$ 都位于素理想 $(frak(p), T) subset A[T]$ 之上。

      另一方面，$b in.not frak(m)_x$，因为它在剩余域中的像正是 $alpha$，而 $0 != alpha$。于是 $x = frak(q)$ 位于 $A[T]$ 的一个不含 $T$ 的素理想之上。这就证明了 $x = frak(q) in Spec(B)$ 是唯一位于 $frak(r) in Spec(D)$ 之上的素理想。

    - $B_(frak(r))$ 在 $D_(frak(r))$ 上有限，并且满足上行性质。因此 $B_(frak(r))$ 的极大理想都位于 $D_(frak(r))$ 的极大理想之上。既然 $B$ 只有一个素理想位于 $frak(r) subset D$ 之上，$B_(frak(r))$ 就只能是局部环，其极大理想为 $frak(q) B_(frak(r))$。于是 $B - frak(q)$ 中每个元素在 $B_(frak(r))$ 中已经可逆，从而 $B_(frak(r)) = B_(frak(q))$。

    - 考虑 $D_(frak(r)) -> B_(frak(r)) -> k(x)$。它的像包含 $k(y)$，也包含 $b$ 在 $k(x)$ 中的像，即 $alpha$，因此这个映射是满射。这说明 $k(frak(r)) = k(x)$。前面已经看到 $B_(frak(r)) = B_(frak(q))$，也就是说：
      $
        D_(frak(r))\/frak(r) D_(frak(r)) = B_(frak(r))\/frak(r) B_(frak(r))
      $
      这里借助有限单射 $D_(frak(r)) -> B_(frak(r))$ 将两边等同。因此 $B_(frak(r)) = D_(frak(r)) + frak(r) B_(frak(r))$；对 $B_(frak(r))\/D_(frak(r))$ 应用 Nakayama 引理，便得 $D_(frak(r)) = B_(frak(r)) = B_(frak(q))$。

    - 由于 $D_(frak(r)) = B_(frak(r))$，再借助铺开（或许可参看 @passage-to-limit-of-morphisms (3)），存在函数 $u in D$ 使 $D_u = B_u$。

    于是把 $Spec(B)$ 缩小为 $Spec(B_u)$，就得到开浸入 $Spec(B) -> Spec(A[T]\/I)$。再把 $B$ 继续缩小，不妨设 $B$ 对应的开集是 $Spec(A[T]\/I)$ 的主仿射开集。也就是说，存在多项式 $h(T) in A[T]$ 使得：
    $
      B cong A[T]_(h(T))\/I
    $
    最后回忆：$I$ 含有首一多项式。
    #suppress-qed
  ]

  于是缩小 $B$，不妨设：
  $
    B = (A[T]\/I)_(h(T))
  $
  且 $Spec(B) -> Spec(A)$ 平展，其中 $h(T) in A[T]$，$I subset A[T]$ 是含有一个 $A[T]$ 中首一多项式的理想，且该理想不含 $h(T)$。

  第二步。把 $I$ 化归为单个首一多项式关系。

  #proof[
    由于 $B\/A$ 平展，
    $
      0 = Omega_(B\/A) = Omega_((A[T]\/I)\/A) otimes_(A[T]\/I) B = (B d T)/((d f: f in I))
    $
    因此可以取 $G(T) in I$ 使 $d G in B^times d T$。也就是说，$G'(T) in A[T]$ 在 $B$ 中的像是单位。

    现在取首一多项式关系 $P(T) in I$，并取足够大的 $N >= 2$，使 $N deg(P(T)) > deg(G(T))$。于是：
    $
      g(T) = P(T)^N + G(T) in I
    $
    上式右端是首一多项式，且 $g'(T) = N P(T)^(N-1) P'(T) + G'(T)$。现在 $P(T) in I$ 在 $B$ 中映为 $0$，故 $g'(T)$ 与 $G'(T)$ 在 $B$ 中的像相同，而这个像是单位。这样就找到了首一多项式关系 $g(T) in I$，且 $g'(T) in B^times$。我们有满射：
    $
      A[T]_(h(T))\/g(T) -> A[T]_(h(T))\/I = B
    $
    它把 $g'(T)$ 映为 $B^times$ 中的元素。因此这个满射穿过 $A[T]_(h(T)g'(T))\/g(T)$ 分解。

    现在把 $f$ 分解为：
    $
      Spec(B) = Spec(A[T]_(h(T))\/I) ->^i Spec(A[T]_(h(T)g'(T))\/g(T)) ->^(f') Spec(A)
    $
    这里 $f'$ 是标准平展态射，因而平展（因为 $g'(T)$ 在 $A[T]_(h(T)g'(T))\/g(T)$ 中可逆），而 $f$ 也平展。于是闭浸入 $i$ 实际上平展，从而是既开又闭的浸入。因此 $Spec(B)$ 是 $Spec(A[T]_(g'(T)h(T))\/g(T)) = Spec((A[T]\/g(T))_(g'(T)h(T)))$ 的标准仿射开集，该开集可由对某个幂等元取逆得到。把这个幂等元与 $g'(T)h(T)$ 相乘，即可看出 $Spec(B) -> Spec(A)$ 是标准平展态射。
    #suppress-qed
  ]
  这就证明了平展态射的局部结构。
]

// 下一个目标是建立光滑态射的局部结构定理。回忆（如 Hartshorne 中那样）如下定义：

// - 设 $f: X -> Y$ 是有限展示的态射。若该态射在 $x$ 处平坦，且 $(Omega_(X\/Y))_x$ 自由（秩为 $d$），则称它在 $x$ 处*光滑（相对维数为 $d$）*。

//   若态射 $f: X -> Y$ 在每一点都光滑，则称它*光滑（相对维数为 $d$）*。等价地，若 $f$ 平坦且 $Omega_(X\/Y)$ 局部自由（秩为 $d$）。

// 于是在这个定义下，平展态射正是相对维数为 $0$ 的光滑态射。关于光滑态射的讨论应参看 Hartshorne 第 3.10 节。

// #definition[
//   A morphism $f: X -> Y$ is said to be *standard smooth* of relative dimension  $d$, if it factors as: 
//   $
//     X ->^j AA^d_Y -> Y
//   $
//   for an etale morphism $j$. A standard smooth morphism of relative dimension $d$ is smooth of relative dimension $d$, since etale morphisms are smooth of relative dimension $0$, and $AA^d_Y -> Y$ is smooth of relative dimension $d$, and smooth morphisms composes. 
// ]

// #theorem(name: <local-struct-of-smooth-morphisms>)[
//   (Local structure of smooth morphisms) For any morphism $f: X -> Y$ smooth of relative dimension $d$ at $x in X$, there exists an open neighborhood $x in U subset X$ s.t. $U -> Y$ is standard smooth. 
// ]
// #proof[
//   Since $Omega_(X\/Y)$ is locally free of rank $d$ at $x$, by shrinking $X$ around $x$, we may assume that $X = Spec(B)$ is affine and $Omega_(X\/Y)$ is free of rank $d$. We may shrink $X$ further to assume that the image of $X$ is contained in an affine open $U subset Y$. Now if we have an etale chart $X -> AA^d_U$, the open immersion gives an etale chart $X -> AA^d_Y$. Thus it is safe to replace $Y$ with $U$ and assume that $Y = Spec(A)$ is affine too. Now that we have an isomorphism $Omega_(B\/A) cong B^(oplus d)$, we may pick $b_1, dots.c, b_d in B$ s.t. $d b_1, dots.c, d b_d$ forms a basis of $Omega_(B\/A)$. These sections define a map: 
//   $
//     Spec(B) -> Spec(A[T_1, dots.c, T_d])
//   $ 
//   by evaluating $T_i$ to $b_i$. We thus have the first exact sequence: 
//   $
//     Omega_(A[T_1,dots.c,T_d]\/A) otimes_(A[T_1,dots.c,T_d]) B -> Omega_(B\/A) -> Omega_(B\/A[T_1,dots.c,T_d]) -> 0
//   $
//   Now $Omega_(A[T_1,dots.c,T_d]\/A) otimes_(A[T_1,dots.c,T_d]) B cong B d T_1 oplus dots.c oplus B d T_d$, and the first map sends $d T_i |-> d b_i$. By our choice of the $b_i$'s, this map is an isomorphism. Thus $Omega_(B\/A[T_1,dots.c,T_d]) = 0$ and so $B$ is unramified over $A[T_1, dots.c, T_d]$. It suffices to show that it is flat. By fiberwise criterion for flatness (#cite-stacks("039E")[Lemma 37.16.4]), it suffices to check that for each point $y in Spec(A)$, the base change: 
//   $
//     X_y = Spec(B otimes_A k(y)) -> AA^d_(k(y))
//   $
//   is flat. Now let $x in X_y$ be a closed point sent to a closed point $u in AA^d_(k(y))$: 

//   - $X_y$ is geometrically regular (hence regular) for being smooth over the field $k(y)$, and $AA^d_(k(y))$ is obviously regular. Thus $cal(O)_(X_y,x)$ and $cal(O)_(AA^d_(k(y)),u)$ are regular local rings. 

//   - $dim(cal(O)_(AA^d_(k(y)),u)) = d$. $X_y$ being smooth of relative dimension $d$ over $k(y)$ has pure dimension $d$, and so $dim(cal(O)_(X_y,x)) = d$. Finally, the fiber: 
//     $
//       cal(O)_(X_y,x)\/frak(m)_u cal(O)_(X_y,x) cong k(x)
//     $
//     since $X_y -> AA^d_(k(y))$ is unramified (by definition), and is $0$-dimensional. Thus: 
//     $
//       dim(cal(O)_(AA^d_(k(y)),u)) + dim(cal(O)_(X_y,x)\/frak(m)_u cal(O)_(X_y,x)) = dim(cal(O)_(X_y,x))
//     $

//   By miracle flatness (#cite-stacks("00R4")[Lemma 10.128.1]), $cal(O)_(X_y,x)$ is flat over $cal(O)_(AA^d_(k(y)),u)$. Thus $X_y -> AA^d_(k(y))$ is flat at every closed point of $X_y$. Since the flat locus is open, this map is flat. We are thereby done. 
// ]

把平展态射与光滑态射的局部结构合起来，便得到下面的推论：

#corollary[
  设态射 $f: X -> Y$ 在 $x in X$ 处光滑，相对维数为 $d$，并记 $y = f(x)$。适当把 $X$ 在 $x$ 附近缩小为 $Spec(B)$、把 $Y$ 在 $y$ 附近缩小为 $Spec(A)$，可使：
  $
    B cong (A[X_1, dots.c, X_d, T]_(h(X,T)))/((g(X,T)))
  $
  使得 $(g(X, T), partial_T g(X, T)) = (1)$ 在 $A[X_1, dots.c, X_d, T]_(h(X,T))$ 中生成单位理想。
]
