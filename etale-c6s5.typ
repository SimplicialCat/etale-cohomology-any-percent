// audit-exception: 展示公式中的 #[...] 文字块内嵌 $f$、$g_lambda$、$g'^(-1)_lambda cal(F)$ 等行内公式，审计按相邻美元符号配对会把块内说明文字切成伪公式段；只译块内说明文字，块内与块外公式逐段核对未变。
#import "void-import.typ": *
== (Reduce) 的证明

本节证明 (Reduce)，这是紧合基变换证明中又一个重要步骤。它让我们可以把一般拉回方块中的基变换，归约为沿 $X -> Spec(A)$ 的基变换以及 $Spec(A)$ 特殊点处的基变换，其中 $A$ 是严格 Hensel 局部环。 

(Reduce) 的证明是一个技术性很强的归约论证，涉及在 Zariski 局部与平展局部上作归约、取极限以及利用拓扑不变性。 

为了说明基变换的平展局部性，我们首先需要一个引理： 

#lemma(name: <pbc-etale-bc>)[
  在拉回方块中： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  其中 $g$ 平展。基变换映射： 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  对任意 $cal(F) in cAb(X_et)$ 都是同构。 
]
#proof[
  我们将用到 @pullback-along-etale-morphism-derived。对任意 $V' in Et_(Y')$，有 
  $
    g^(-1) R^q f_* cal(F) (V') = R^q f_* cal(F) (V') = (V |-> H^q (f^(-1) (V), cal(F)))^\# (V')
  $
  其中 $(V |-> H^q (f^(-1) (V), cal(F))) in cPAb(Y_et)$；而 
  $
    R^q f'_* g'^(-1) cal(F) (V') = (V' |-> H^q (f'^(-1) (V'), g'^(-1) cal(F)))^\# (V')
  $
  其中 $(V' |-> H^q (f^(-1) (V'), g'^(-1) cal(F))) in cPAb(Y'_et)$。因此只需证明 
  $
    g^(-1) ((V |-> H^q (f^(-1) (V), cal(F)))^\#) = (V' |-> H^q (f^(-1) (V'), g'^(-1) cal(F)))^\# in cAb(Y'_et)
  $ 
  注意 
  $
    g^(-1)_cPSh (V |-> H^q (f^(-1) (V), cal(F))) = (V' |-> H^q (f'^(-1) (V'), g'^(-1) cal(F)))
  $
  这里用了 @pullback-along-etale-morphism-derived；结论则由 @pullback-first-props (3) 得到。 
]

我们还需要一条极限公式，供后面取极限的论证使用。 

首先，我们建立复合极限公式 @limit-formula-composite 的预层版本： 

#lemma(name: <limit-formula-composite-pab>)[
  设 ${X_i}_(i in I)$ 是拟紧拟分离概形构成的逆向系统，其中所有过渡映射 $u_(i,j): X_i -> X_j$（$i>=j$）都仿射。令：
  $
    X = invlim_(i in I) X_i
  $
  投影为 $v_i: X -> X_i$。若以下两条成立，则称 $(cal(P)_i, psi_(i,j))$ 为逆向系统 ${X_i}$ 的*预层系统* (system of presheaves)：
  
  - 每个 $cal(P)_i in cPAb((X_i)_et)$ 都是 $X_i$ 上的平展交换群预层。
  
  - 对任意 $i>=j$，$psi_(i,j): u_(i,j,cPSh)^(-1) cal(P)_j -> cal(P)_i$ 是预层态射，且对 $i>=j>=k$ 满足： #h(1fr)
    $
      psi_(i,k) = psi_(i,j) compose u_(i,j,cPSh)^(-1) psi_(j,k)
    $
  
  这个预层系统的*极限预层* (limit presheaf) 定义为：
  $
    cal(P) := dirlim_(i in I) v_(i,cPSh)^(-1) cal(P)_i
  $
  其中对 $i>=j$，过渡映射 $v_(j,cPSh)^(-1) cal(P)_j -> v_(i,cPSh)^(-1) cal(P)_i$ 由 $v_(i,cPSh)^(-1) psi_(i,j)$ 诱导。于是对任何拟紧拟分离的 $U in Et_X$，都存在某个 $k$ 与拟紧拟分离的 $U_k in Et_(X_k)$，使前者可以由后者经基变换得到；典范态射：
  $
    dirlim_(i>=k) cal(P)_i (U_i) -> cal(P)(U)
  $
  是同构。 
]
#proof[
  证明与 @limit-formula-composite 类似，只是这里要同时用到预层的极限公式与概形的极限公式。预层的极限公式并不是一个命题，而是这样一个事实：预层范畴中的余极限逐截面计算。 

  现在： 
  $
    cal(P)(U) = dirlim_(j in I) v_(j,cPSh)^(-1) cal(P)_j (U) = dirlim_(j>=k) v_(j,cPSh)^(-1) cal(P)_j (U)
  $
  由 @limit-formula-for-schemes-pab（应当把它看成预层上的概形极限公式）： 
  $
    v_(j,cPSh)^(-1) cal(P)_j (U) = dirlim_(i>=j) u_(i,j,cPSh)^(-1) cal(P)_j (U_i)
  $
  于是， 
  $
    cal(P)(U) = dirlim_(j>=k) dirlim_(i>=j) u_(i,j,cPSh)^(-1) cal(P)_j (U_i)
  $
  由于 $I$ 是正向集，这个二重极限中的每一对 $(j,i)$ 都被 $(i,i)$ 支配。换言之，对应于 $i = j >= k$ 的那些对象在这个余极限的指标范畴中共尾。因此， 
  $
    cal(P)(U) = dirlim_(j>=k) dirlim_(i>=j) u_(i,j,cPSh)^(-1) cal(P)_j (U_i) = dirlim_(i>=k) cal(P)_i (U_i)
  $
  证毕。 
]

接下来我们建立基变换的极限公式，即对基变换取极限。 

#proposition(name: <limit-formula-for-base-change>)[
  (基变换的极限公式) 设： 
  $
    X = invlim_(i in I) X_i, S = invlim_(i in I) S_i
  $
  是拟紧拟分离概形的逆向极限，过渡映射 $f_(i,j): X_i -> X_j$ 与 $h_(i,j): S_i -> S_j$（$i>=j$）都仿射。记投影为 $f_i: X -> X_i, h_i: S -> S_i$。 

  假设给定态射 $g_i: X_i -> S_i$ 与 $g: X -> S$，使得下面的图表 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYX2kiXSxbMSwxLCJTX2kiXSxbMCwyLCJYX2oiXSxbMSwyLCJTX2oiXSxbMCwwLCJYIl0sWzEsMCwiUyJdLFswLDEsImdfaSJdLFsyLDMsImdfaiIsMl0sWzAsMiwiZl8oaSxqKSIsMl0sWzEsMywiaF8oaSxqKSJdLFs0LDUsImciXSxbNSwxLCJoX2kiXSxbNCwwLCJmX2kiLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X_i$])
    node((0, -1), [$S_i$])
    node((-1, 0), [$X_j$])
    node((0, 0), [$S_j$])
    node((-1, -2), [$X$])
    node((0, -2), [$S$])
    node((-0.7, -1.7), $cart$)
    node((-0.7, -0.7), $cart$)
    edge((-1, -1), (0, -1), [$g_i$], label-side: left, "->")
    edge((-1, 0), (0, 0), [$g_j$], label-side: right, "->")
    edge((-1, -1), (-1, 0), [$f_(i,j)$], label-side: right, "->")
    edge((0, -1), (0, 0), [$h_(i,j)$], label-side: left, "->")
    edge((-1, -2), (0, -2), [$g$], label-side: left, "->")
    edge((0, -2), (0, -1), [$h_i$], label-side: left, "->")
    edge((-1, -2), (-1, -1), [$f_i$], label-side: right, "->")
  }))
  中所有方块都是拉回方块。那么，给定 ${X_i}$ 的一个层系统 $(cal(F)_i, psi_(i,j))$（含义同 @limit-formula-composite），存在典范同构： 
  $
    dirlim_(i in I) h_i^(-1) R^q g_(i,*) cal(F)_i -> R^q g_* cal(F)
  $
  其中过渡映射 $h_j^(-1) R^q g_(j,*) cal(F)_j -> h_i^(-1) R^q g_(i,*) cal(F)_i$ 是如下复合： 
  $
    h_j^(-1) R^q g_(j,*) cal(F)_j = h_i^(-1) h_(i,j)^(-1) R^q g_(j,*) cal(F)_j ->^BC h_i^(-1) R^q g_(i,*) f_(i,j)^(-1) cal(F)_j ->^(h_i^(-1) R^q g_(i,*) psi_(i,j)) h_i^(-1) R^q g_(i,*) cal(F)_i
  $
  其中 $BC$ 表示基变换映射。类似地，典范同构中从正向极限出发的映射则由下式构造： 
  $
    h_i^(-1) R^q g_(i,*) cal(F)_i ->^BC R^q g_* f_i^(-1) cal(F)_i ->^(R^q g_* psi_i) R^q g_* cal(F)
  $
]
#proof[
  取： 
  $
    cal(P)_i = (V_i |-> H^q (X_i times_(S_i) V_i, cal(F)_i)) in cPAb((S_i)_et) \
    cal(P) = (V |-> H^q (X times_S V, cal(F))) in cPAb(S_et)
  $
  于是： 
  $
    R^q g_(i,*) cal(F)_i = cal(P)_i^\#, R^q g_* cal(F) = cal(P)^\#
  $
  现在： 
  $
    dirlim_(i in I) h_i^(-1) R^q g_(i,*) cal(F)_i = dirlim_(i in I) h_i^(-1) cal(P)_i^\# = (dirlim_(i in I \ cPAb) h_(i,cPSh)^(-1) cal(P)_i)^\#
  $
  这里用了 @pullback-first-props (3) 以及 $(-)^\#$ 作为左伴随与余极限交换这一事实。现在要证： 
  $
    (dirlim_(i in I \ cPAb) h_(i,cPSh)^(-1) cal(P)_i)^\# = cal(P)^\#
  $
  由于 $S$ 拟紧拟分离，只需证明这两个层在拟紧拟分离的 $V in Et_S$ 上的截面一致。而 $caron(H)^0 (V, -)$ 只用 $Et_S$ 中的拟紧拟分离对象来计算（正如 @limit-formula-for-schemes-0 的证明中那个共尾系统 $cal(S)$），故只需证明：对拟紧拟分离的 $V in Et_S$， 
  $
    (dirlim_(i in I \ cPAb) h_(i,cPSh)^(-1) cal(P)_i)(V) = cal(P)(V)
  $
  左边可以用 @limit-formula-composite-pab 计算：设 $V in Et_S$ 由拟紧拟分离的 $V_k in Et_(S_k)$ 经基变换得到，则： 
  $
    (dirlim_(i in I \ cPAb) h_(i,cPSh)^(-1) cal(P)_i)(V) = dirlim_(i>=k) cal(P)_i (V_i) = dirlim_(i>=k) H^q (X_i times_(S_i) V_i, cal(F)_i)
  $
  而 $cal(P)(V) = H^q (X times_S V, cal(F))$。注意 $S_i times_(S_k) (X_k times_(S_k) V_k) = X_i times_(S_i) V_i$，该式去掉下标 $i$ 后所得的等式同样成立，故由复合极限公式 @limit-formula-composite 即得： 
  $
    dirlim_(i>=k) H^q (X_i times_(S_i) V_i, cal(F)_i) = H^q (X times_S V, cal(F))
  $
  证毕。 
]

#theorem(name: <pbc-reduce>)[
  (Reduce) 若 $Y', Y$ 局部 Noether，则
  $
        & BC(X ->^f Y, Y' ->^g Y) \
    <== & (BC_* (X times_Y Spec(A) -> Spec(A)), forall Spec(A) -> Y, forall A #[Noether 严格 Hensel])
  $
  说得直白些：基变换对下面的拉回方块成立， 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  只要对每个态射 $Spec(A) -> Y$（其中 $A$ 是 Noether 严格 Hensel 环），基变换沿 $X times_Y Spec(A) -> Spec(A)$ 成立，且在 $Spec(A)$ 的特殊点上也成立。  
]
#proof[
  #lemma(name: <pbc-reduce-etale-local>)[
    基变换关于 $Y'$ 是平展局部的。换言之，考虑逐次基变换的图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYJyJdLFsxLDEsIlknIl0sWzAsMiwiWCJdLFsxLDIsIlkiXSxbMSwwLCJZJyciXSxbMCwwLCJYJyciXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdLFs1LDQsImYnJyJdLFs0LDEsImgiXSxbNSwwLCJoJyciLDJdXQ==
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((1, -1), [$Y''$])
      node((0, -1), [$X''$])
      edge((0, 1), (1, 1), [$f$], label-side: left, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      edge((0, -1), (1, -1), [$f''$], label-side: left, "->")
      edge((1, -1), (1, 0), [$h$], label-side: left, "->")
      edge((0, -1), (0, 0), [$h'$], label-side: right, "->")
    }))
    其中 $h: Y'' -> Y'$ 是满射且平展。则基变换对下方方块成立，当且仅当它对整个大矩形成立。 
  ]
  #proof[
    ($==>$) 就是 (Comp) @pbc-comp (2)，因此只需证明 ($<==$)。对任意挠层 $cal(F) in cAb(X_et)$，要证基变换映射： 
    $
      g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
    $
    是同构。由 @surjective-pullback-conservative，只需证明： 
    $
      h^(-1) g^(-1) R^q f_* cal(F) -> h^(-1) R^q f'_* g'^(-1) cal(F)
    $
    是同构。由 @pbc-etale-bc，基变换态射 $h^(-1) R^q f'_* g'^(-1) cal(F) -> R^q f''_* h'^(-1) g^(-1) cal(F)$ 是同构（这里 $g'^(-1) cal(F)$ 是挠层，依据是 @pullback-of-torsion-sheaf）。由基变换态射的自然性，把这个同构与上面的态射复合，得到： 
    $
      h^(-1) g^(-1) R^q f_* cal(F) -> h^(-1) R^q f'_* g'^(-1) cal(F) ->^tilde R^q f''_* h'^(-1) g^(-1) cal(F)
    $
    它就是挠层 $cal(F)$ 沿大矩形的基变换态射，从而是同构。于是 $h^(-1) g^(-1) R^q f_* cal(F) -> h^(-1) R^q f'_* g'^(-1) cal(F)$ 是同构，证毕。 
  ]
  现在取 $Y'$ 的一个覆盖 ${Y''_i}$，其中每个 $Y''_i$ 都是仿射开集，且它在 $Y'$ 中的像含于 $Y'$ 的某个仿射开集。取 $Y'' = union.sq.big_i Y''_i$，则由上一个引理，可以把 $g: Y' -> Y$ 换成 $Y'' -> Y$。由不交并的结构，只需证明对每个 $i$，基变换沿 $f: X -> Y$ 与 $Y''_i -> Y$ 成立。换言之，不妨设 $Y'$ 仿射，且它在 $Y$ 中的像含于某个仿射开集 $Y_1$。现在 $g: Y' -> Y$ 分解为 $Y' ->^(g_1) Y_1 ->^i Y$。考虑逐次基变换的图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYXzEiXSxbMSwxLCJZXzEiXSxbMCwyLCJYIl0sWzEsMiwiWSJdLFsxLDAsIlknIl0sWzAsMCwiWCciXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJpIl0sWzAsMiwiaSciLDJdLFs1LDQsImYnJyJdLFs0LDEsImdfMSJdLFs1LDAsImcnXzEiLDJdXQ==
  #align(center, diagram({
    node((0, 1), [$X_1$])
    node((1, 1), [$Y_1$])
    node((0, 2), [$X$])
    node((1, 2), [$Y$])
    node((1, 0), [$Y'$])
    node((0, 0), [$X'$])
    edge((0, 2), (1, 2), [$f$], label-side: left, "->")
    edge((0, 1), (1, 1), [$f_1$], label-side: left, "->")
    edge((1, 1), (1, 2), [$i$], label-side: left, "->")
    edge((0, 1), (0, 2), [$i'$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
    edge((1, 0), (1, 1), [$g_1$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g'_1$], label-side: right, "->")
  }))

  由 @pbc-etale-bc，由于 $i$ 是开浸入，从而是平展的，故基变换对下方方块成立。于是由 (Comp) @pbc-comp (2)，只需证明基变换对上方方块成立。由于 $f_1$ 是 $f$ 的基变换，$f_1$ 沿任一 $Spec(A) -> Y_1$（其中 $A$ 是 Noether 严格 Hensel 环）的基变换，也是 $f$ 沿 $Spec(A) -> Y_1 -> Y$ 的基变换。因此假设对 $f_1$ 依然成立。于是把 $f$ 换成 $f_1$、$g$ 换成 $g_1$，不妨设： 

  - $Y' = Spec(B'), Y = Spec(B)$ 都仿射，从而 $B'$ 是 $B$-代数，且 $B, B'$ 都 Noether（因为最初 $Y, Y'$ 就是 Noether 的）。 

  我们断言：若 (Reduce) 在 $g: Spec(B') = Y' -> Y = Spec(B)$ 有限型时总成立，则它在一般情形也成立。 

  #proof_[断言的证明][
    由上面的论证，不妨设 $g: Spec(B') = Y' -> Y = Spec(B)$ 已经是两个仿射概形之间的态射。现在写： 
    $
      B' = union.big_lambda B'_lambda = dirlim_(lambda) B'_lambda 
    $
    其中 ${B'_lambda}$ 跑遍 $B'$ 的所有有限型 $B$-子代数，按包含关系排序。于是： 
    $
      Y' = invlim_lambda Y'_lambda, Y'_lambda = Spec(B'_lambda)
    $
    于是基变换可以取极限： 
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCdfbGFtYmRhIl0sWzEsMSwiWSdfbGFtYmRhIl0sWzAsMiwiWCdfbXUiXSxbMSwyLCJZJ19tdSJdLFsxLDMsIlkiXSxbMCwzLCJYIl0sWzcsNiwiZiIsMl0sWzQsNSwiZidfbXUiXSxbMiwzLCJmJ19sYW1iZGEiXSxbMCwxLCJmJyJdLFsxLDMsImhfbGFtYmRhIl0sWzMsNSwiZ18obGFtYmRhLG11KSJdLFs1LDYsImdfbXUiXSxbNCw3LCJnJ19tdSIsMl0sWzIsNCwiZydfKGxhbWJkYSxtdSkiLDJdLFswLDIsImgnX2xhbWJkYSIsMl1d
    #align(center, diagram({
      node((0, -2), [$X'$])
      node((1, -2), [$Y'$])
      node((0, -1), [$X'_lambda$])
      node((1, -1), [$Y'_lambda$])
      node((0, 0), [$X'_mu$])
      node((1, 0), [$Y'_mu$])
      node((1, 1), [$Y$])
      node((0, 1), [$X$])
      node((0.3, -1.7), $cart$)
      node((0.3, -0.7), $cart$)
      node((0.3, 0.3), $cart$)
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'_mu$], label-side: left, "->")
      edge((0, -1), (1, -1), [$f'_lambda$], label-side: left, "->")
      edge((0, -2), (1, -2), [$f'$], label-side: left, "->")
      edge((1, -2), (1, -1), [$h_lambda$], label-side: left, "->")
      edge((1, -1), (1, 0), [$g_(lambda,mu)$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g_mu$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g'_mu$], label-side: right, "->")
      edge((0, -1), (0, 0), [$g'_(lambda,mu)$], label-side: right, "->")
      edge((0, -2), (0, -1), [$h'_lambda$], label-side: right, "->")
    }))
    其中每个 $g_mu$ 都有限型。由于 $g$ 有限型时 (Reduce) 成立，可知沿 $f$ 与 $g_mu$（即上图最下方的方块）的基变换成立。现在应用基变换的极限公式（@limit-formula-for-base-change）： 
    $
      R^q f'_* g'^(-1) cal(F) &= dirlim_lambda h_lambda^(-1) R^q f'_(lambda,*) g'^(-1)_lambda cal(F) #[由基变换的极限公式] \
      &= dirlim_lambda h_lambda^(-1) g_lambda^(-1) R^q f_* cal(F) \
      & #[因为基变换沿 $f$ 与 $g_lambda$ 成立，且 $g'^(-1)_lambda cal(F) $ 是挠层，这里用到 @pullback-of-torsion-sheaf] \
      &= dirlim_lambda g^(-1) R^q f_* cal(F) = g^(-1) R^q f_* cal(F)
    $
    于是基变换沿 $f$ 与 $g$ 成立。 
    #suppress-qed
  ]
  因此不妨设 $g$ 有限型。由 @stalks-detects-properties 与 @very-dense-sets-of-pts，只需证明：对任意有限型点 $y' in Y'$，挠层 $cal(F)$ 的基变换映射 $g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)$ 在 $ol(y') = Spec(k(y')^sep)$ 处是同构，其中 $k(y')^sep$ 是 $k(y')$ 的一个固定可分闭包。令 $y = g(y')$，再令 $ol(y) = Spec(k(y)^sep)$，其中 $k(y)^sep$ 是 $k(y)$ 在 $k(y')^sep$ 中的可分闭包。（之所以显式选取，是为了能用 $cal(O)_(Y,g(y))$ 关于 $k(y) -> k(y)^sep$ 的严格 Hensel 化，具体算出 $R^q f_* cal(F)$ 在 $g(ol(y'))$ 处的茎。）

  现在来计算： 
  $
    (g^(-1) R^q f_* cal(F))_(ol(y')) &= (R^q f_* cal(F))_(g(ol(y'))) = H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y)))) \
    &= H^q (X times_Y ol(y), cal(F)|_(X times_Y ol(y)))
  $
  由于 $tilde(Y)_(ol(y)) = Spec(cal(O)_(Y,y)^#[sh])$ 是严格 Hensel 局部环的谱；由 @permanence-of-properties-under-henselization (0)（这里用到 $Y$ 是 Noether 的）可知该严格 Hensel 局部环也是 Noether 的。于是按假设，限制映射 $H^q (X times_Y tilde(Y)_(ol(y)), cal(F)|_(X times_Y tilde(Y)_(ol(y)))) -> H^q (X times_Y ol(y), cal(F)|_(X times_Y ol(y)))$ 是同构。同样地， 
  $
    (R^q f'_* g'^(-1) cal(F))_(ol(y')) &= H^q (X' times_(Y') tilde(Y')_(ol(y')), cal(F)|_(X' times_(Y') tilde(Y')_(ol(y')))) = H^q (X times_Y tilde(Y')_(ol(y')), cal(F)|_(X times_Y tilde(Y')_(ol(y')))) \
    &= H^q (X times_Y ol(y'), cal(F)|_(X times_Y ol(y')))
  $
  这里用了严格 Hensel 的假设。 
  
  最后注意，因 $y'$ 是有限型点，$y': Spec(k(y')) -> Y'$ 有限型。又因 $g$ 有限型，$Spec(k(y')) -> Y' ->^g Y$ 有限型。取该复合态射在 $y in Y$ 上的纤维，便知 $Spec(k(y')) -> Spec(k(y))$ 有限型。换言之，$k(y')\/k(y)$ 是域扩张，且作为环扩张是有限型的。由 Hilbert 强零点定理，$k(y')\/k(y)$ 是有限扩张。于是 $k(y')^sep\/k(y)^sep$ 是纯不可分代数扩张。因此 $ol(y') -> ol(y)$ 是泛同胚，从而： 
  $
    (g^(-1) R^q f_* cal(F))_(ol(y')) = H^q (X times_Y ol(y), cal(F)|_(X times_Y ol(y))) = H^q (X times_Y ol(y'), cal(F)|_(X times_Y ol(y'))) = (R^q f'_* g'^(-1) cal(F))_(ol(y'))
  $
  这里用了拓扑不变性。证毕。 
]
