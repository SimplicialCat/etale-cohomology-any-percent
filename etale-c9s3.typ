// audit-exception: 展示公式内的 #[...] 文字块嵌有多段行内公式，朴素配对会把块内散文切成伪公式段（如 $-good open dense of$、$whenever$）；译文只改文字说明，块内公式与全部数学逐段核对未变。
#import "void-import.typ": *

== 一般基变换与有限性

本节我们建立一般基变换定理：设 $f$ 是底上有限型概形之间的态射，则 $R f_*$ 的构造保持 $D^b_c$，并且在把底缩小到某个稠密开集之后与基变换相容。作为应用，我们建立投影公式与 Künneth 公式，不过针对的不是 $R f_!$，而是 $R f_*$。在其证明中，经过一串归约之后，我们会用 Poincaré 对偶打通最后一步。 

本节的证明方法紧密沿用 @cite-lei-fu[Section 9.3] 的做法，只调整了叙述顺序、作了些微改动。归根结底，这仍是 @cite-SGA4half 的方法。 

#theorem(name: <generic-base-change>)[
  (一般有限性与基变换) 设 $Lambda$ 是 $n$-挠 Noether 环，$S$ 是 Noether 的 $ZZ[n^(-1)]$-概形，$f: X -> Y$ 是有限型 $S$-概形之间的态射。则对任意 $cal(K) in D^b_c (X_et, Lambda)$，存在稠密开集 $U subset S$，使得： 

  - $R f_(U,*) (cal(K)|_(X_U)) in D^b_c ((Y_U)_et, Lambda)$，其中 $f_U: X_U -> Y_U$ 是 $f$ 沿 $U -> S$ 的基变换； 

  - 对任意拉回图表：#h(1fr)
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      // node((0.3, 0.3), [$cart$])
      node((2, 1), [$S$])
      node((2, 0), [$S'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 1), (2, 1), "->")
      edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
      edge((2, 0), (2, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
    }))
    其中 $g(S') subset U$， 
    $
      g_Y^(-1) R f_* cal(K) -> R f'_* g_X^(-1) cal(K)
    $
    是同构。 
]
#proof[
  #notation[
    在本证明中，若开子集 $U subset S$ 使上述定理成立，就称它为 *$(f, cal(K), S)$-好*开集。可以看出： 

    - 若 $f$ 紧合，则 $S$ 本身是 $(f, cal(K), S)$-好的。（这来自紧合基变换以及 $R f_*$ 的有限性（@finiteness-of-lower-shriek）。）

    - 对 $X ->^f Y ->^g Z$，若 $U subset S$ 是 $(f, cal(K), S)$-好的，则 $U$ 是 $(g_U, R f_(U,*) (cal(K)|_(X_U)), S)$-好的，当且仅当它是 $(g compose f, cal(K), S)$-好的。这可以直接由定义验证。 

      // 反之，若 $U subset S$ 是 $(g compose f, cal(K))$-好的且是 $(f, cal(K))$-好的，则它也是 $(g, R f_(U,*) (cal(K)|_(X_U)))$-好的。 

    - 给定 $D^b_c (X_et, Lambda)$ 中的特殊三角 $cal(K)_1 -> cal(K)_2 -> cal(K)_3 ->^(+1)$，若 $U subset S$ 对 $i=1,2$ 都是 $(f, cal(K)_i, S)$-好的，则它也是 $(f, cal(K)_3, S)$-好的。 
  ]

  注意： 

  - 设 $S$ 的不可约分支为 $S_1, dots.c, S_m$，并令 $U = S - union.big_(i<j) (S_i inter S_j)$。则 $U$ 是 $S$ 的稠密开集，且是其不可约分支的不交并。把 $S$ 缩小到 $U$，便可在每个不可约分支上分别论证，从而不妨设 $S$ 不可约。再基变换到 $S$ 的约化并利用拓扑不变性，于是从今往后不妨设 $S$ 整、其泛点为 $sigma = Spec(K(S))$。把 $S$ 缩小到任一仿射开集，还可设 $S$ 仿射。 

  - 这个问题在 $Y$ 上是局部的。事实上，取 $Y$ 的一个由有限多个开集组成的仿射覆盖 ${Y_i}$，把 $f$ 基变换为 $f_i: X_i -> Y_i$，并置 $cal(K)_i := cal(K)|_(X_i)$。此时若稠密开集 $U_i subset S$ 都是 $(f_i, cal(K)_i, S)$-好的，则容易验证 $inter.big_i U_i$ 是 $(f, cal(K), S)$-好的。因此，必要时总可以把 $f$ 基变换到 $Y$ 的某个仿射开集上。 

  #lemma[
    以下条件等价： 

    - 对有限型 $S$-概形之间的每个态射 $f: X -> Y$（满足 $dim(X_sigma) <= d$）以及每个 $cal(K) in D^b_c (X_et, Lambda)$，都存在 $S$ 的 $(f, cal(K), S)$-好稠密开集； 

    - 对有限型 $S$-概形之间的每个开浸入 $f: X -> Y$（满足 $dim(X_sigma) <= d$、$Y$ 仿射且 $f$ 支配）以及每个 $cal(K) in D^b_c (X_et, Lambda)$，都存在 $S$ 的 $(f, cal(K), S)$-好稠密开集。 
  ]
  #proof[
    ($==>$) 是同义反复，故只证 ($<==$)。 
    先化归到 $X$ 仿射的情形。假定 $X$ 与 $Y$ 都仿射的情形以及 $f$ 为开浸入的情形都已处理完毕。置： 
    $
      cal(S) = {Z subset X #[closed]: #[对一切 $cal(K)_Z in D^b_c (Z_et, Lambda) $，都存在 $S$ 的 $(f, i_(Z,*) cal(K)_Z, S) $-好稠密开集]}
    $
    其中 $i_Z: Z -> X$ 是闭浸入，这里给 $Z$ 赋予既约子概形结构。我们想用 $cal(S)$ 作 Noether 归纳，证明 $X in cal(S)$。设 $Z subset X$ 闭，且对任一真闭子集 $W subset.neq Z$ 都有 $W in cal(S)$。我们要证 $Z in cal(S)$ 也成立。 
    
    - 注意 $S$ 的 $(f, i_(Z,*) cal(K)_Z, S)$-好开集不过是 $(f compose i_Z, cal(K)_Z, S)$-好稠密开集。于是把 $f$ 换成 $f compose i_Z$，便可设 $Z = X$。取仿射开集 $V subset X$，其补闭集为 $W subset X$，并取浸入 $j: V -> X, i: W -> X$。对 $cal(K) in D^b_c (X_et, Lambda)$，考虑带支集截面三角： 
      $
        i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
      $
      现在： 

      - $j$ 是开浸入，且 $j^(-1) cal(K) in D^b_c (V_et, Lambda)$。又有 $dim(V_sigma) <= dim(X_sigma) <= d$。于是由开浸入情形，存在 $(j, j^(-1) cal(K), S)$-好的稠密开集 $U subset S$。把 $S$ 缩小到这个开集，便可不妨设 $S$ 是 $(j, j^(-1) cal(K), S)$-好的，特别地 $R j_* j^(-1) cal(K) in D^b_c (X_et, Lambda)$。 

      - 现在 $i_* R i^! cal(K) in D^b_c (X_et, Lambda)$，故由 @finite-morphisms-and-constructible-sheaves 知 $R i^! cal(K) in D^b_c (W_et, Lambda)$。于是由 $W in cal(S)$，存在 $(f, i_* R i^! cal(K), S)$-好的稠密开集 $U subset S$。把 $S$ 也缩小到这个开集。 

      - 由于 $f compose j: V -> Y$ 来自仿射概形 $V$，且 $dim(V_sigma) <= dim(X_sigma) <= d$，由仿射情形，存在 $(f compose j, j^(-1) cal(K), S)$-好的稠密开集 $U subset S$。而 $S$ 已是 $(j, j^(-1) cal(K), S)$-好的，故 $U$ 是 $(f, R j_* j^(-1) cal(K), S)$-好的。 

      于是由这个三角可知 $U$ 是 $(f, cal(K), S)$-好的。故 $X in cal(S)$。 
    
    因此，只需处理以下两种情形： 

    - $f: X -> Y$ 是开浸入，且 $dim(X_sigma) <= d$； 

    - $f: X -> Y$ 中 $X$ 仿射，且 $dim(X_sigma) <= d$。 

    假定第一种情形成立。至于第二种情形，$f$ 是有限型的分离态射，故 $f$ 有紧化 $X ->^j ol(X) ->^(ol(f)) Y$，其中 $j$ 是开浸入、$ol(f)$ 紧合。由于 $ol(f)$ 紧合，对一切 $cal(L) in D^b_c (ol(X)_et, Lambda)$，$S$ 都是 $(ol(f), cal(L), S)$-好的。现在 $dim(X_sigma) <= d$，故可应用第一种开浸入情形，得到稠密开集 $U subset S$，它是 $(j, cal(K), S)$-好的。于是 $U$ 是 $(ol(f) compose j, cal(K), S)$-好的，证毕。 

    这样只剩下 $f: X -> Y$ 是开浸入且 $dim(X_sigma) <= d$ 的情形。由问题在 $Y$ 上的局部性，还可进一步设 $Y$ 仿射。 

    最后，把开浸入 $f$ 经其概形像作分解，即可写成像稠密的开浸入与闭浸入的复合。闭浸入的情形由紧合基变换处理，故不妨设 $f$ 的像稠密。这就归结到假设中的情形。 
  ]

  于是对 $d$ 归纳，不妨设： 

  - $f: X -> Y$ 是有限型 $S$-概形之间的开浸入，$dim(X_sigma) = d$，$Y$ 仿射且 $f$ 支配； 

  - 对有限型 $S$-概形之间每个一般的态射 $f: X -> Y$（满足 $dim(X_sigma) <= d-1$），每个复形 $cal(K) in D^b_c (X_et, Lambda)$ 都存在 $S$ 的 $(f, cal(K), S)$-好稠密开集。 

  当 $d <= 0$ 时，我们断言 $X_sigma = Y_sigma$。 
  
  - 事实上，$Y_sigma$ 的泛点对应于 $Y$ 中那些支配 $S$ 的不可约分支的泛点；而 $X -> Y$ 支配，故这些点都落在 $X$ 里。于是包含映射 $X_sigma -> Y_sigma$ 支配。但 $dim(X_sigma) = 0$，所以 $X_sigma$ 只能由 $Y_sigma$ 的有限多个闭点组成；故 $Y_sigma = X_sigma$。 

  现在应用 @passage-to-limit-of-morphisms (3)，可知存在稠密开集 $U subset S$，使得 $X_U = Y_U$。把 $S$ 缩小到这个稠密开集，$f$ 就变成 $id$，问题变得平凡。 

  归纳的起始步至此处理完毕，于是不妨设 $d >= 1$，真正进入归纳步。我们断言：只需处理 $X$ 有一个在 $S$ 上光滑的稠密开集的情形。 

  #proof_[断言的证明][
    设 $L$ 是 $S$ 的函数域 $K = K(S)$ 的完全闭包。 
  
    现在考虑 $f$ 沿 $Spec(L) -> S$ 的基变换 $f_L: X_L -> Y_L$。约化 $(X_L)_#[red]$ 是域 $L$ 上的有限型概形，故其正则轨迹是开集。由于 $X'_L = (X_L)_#[red]$ 既约，在它的每个泛点处，局部环都是域，因此 $X'_L$ 的正则轨迹稠密。于是存在支配的开浸入 $W_L -> X'_L$。而 $W_L$ 在完全域 $L$ 上正则，从而在 $Spec(L)$ 上光滑。也就是说，$W_L -> X'_L -> Spec(L)$ 光滑。 

    于是如在 @finiteness-of-lower-shriek 的证明中那样，可以写成： 
    $
      Spec(L) = dirlim_lambda T_lambda
    $
    其中每个 $T_lambda$ 都是整的仿射 $S$-概形，并且存在主仿射开集 $S_lambda subset S$，使得 $T_lambda -> S_lambda$ 有限、满射且根性，从而是泛同胚。现在看下面这串 $L$-概形之间的态射： 
    $
      W_L -> X'_L -> X_L -> Y_L -> Spec(L)
    $
    它们必定来自基变换： 
    $
      W_lambda -> X'_lambda -> X_lambda -> Y_lambda -> T_lambda
    $
    即对某个阶段 $lambda$，沿 $Spec(L) -> T_lambda$ 作基变换。增大 $lambda$，便可不妨设： 

    - 由 @passage-to-limit-of-morphisms (3)，$X_lambda -> Y_lambda -> T_lambda$ 恰是 $X ->^f Y -> S$ 的基变换。 

    - 由 @passage-to-limit-of-properties (3c)，$W_lambda -> T_lambda$ 光滑。 

    - 由 @passage-to-limit-of-properties (3f)，$W_lambda -> X'_lambda$ 是开浸入。 

    - 由 @passage-to-limit-of-properties (2b)(3g)，$X'_lambda -> X_lambda$ 是满的闭浸入，特别地是泛同胚。 

    - 最后，还可以令 $W_lambda -> X'_lambda$ 支配。事实上，取它的概形像 $W_lambda -> ol(W_lambda) -> X'_lambda$。由于 $W_L -> X'_L$ 支配，基变换到 $L$ 便知 $(ol(W)_lambda)_L -> (X'_lambda)_L$ 是恒等映射。而 $L\/Frac(T_lambda)$ 是纯不可分扩张，定义了泛同胚，所以 $ol(W_lambda) -> X'_lambda$ 在 $T_lambda$ 上的泛纤维上支配。于是存在主仿射开集 $T_mu subset T_lambda$（它也是族 ${T_lambda}$ 中的概形），使得 $(ol(W)_lambda) times_(T_lambda) T_mu -> X'_mu$ 是恒等映射。然而这个闭浸入恰是 $W_mu -> X'_mu$ 的概形像，故 $W_mu -> X'_mu$ 必定支配。 

    现在把 $S$ 缩小到 $S_lambda$，便可设 $T_lambda -> S$ 满射。它还是有限根性的，从而是泛同胚。由拓扑不变性，还可把 $S$ 基变换到 $T_lambda$，并把 $X_lambda$ 换成 $X'_lambda$，而问题不变。也就是说，把 $S$ 换成 $T_lambda$、把 $f: X -> Y$ 换成 $X'_lambda -> Y'_lambda$（注意 $W_lambda$ 是 $X'_lambda$ 中在 $T_lambda$ 上光滑的稠密开集），便完成了这一步。 
  ]
  设 $W subset X$ 是使 $W -> S$ 光滑的稠密开集。取 $cal(K) in D^b_c (X_et, Lambda)$，我们要找 $S$ 的 $(f, cal(K), S)$-好稠密开集。对 $cal(K)$ 作截断，只需证明：对 $X$ 上任意 $Lambda$-模可构造层 $cal(F)$，都存在 $S$ 的 $(f, cal(F), S)$-好稠密开集。 

  进一步缩小 $W$，不妨设 $W subset X$ 是使 $cal(F)|_W$ 局部常值的稠密开集。（比如，在 $X$ 的每个使 $cal(F)$ 成为 l.c.c. 的分层上，围绕每个泛点各取一个开集即可。）于是存在平展覆盖 $pi: W_1 -> W$，使得 $cal(F)|_(W_1)$ 在每个连通分支上常值。 

  对 $W$ 的每个泛点，其局部环是 Artin 局部环，故其约化是域。到域上的每个拟紧平展映射都是有限平展的，因此由拓扑不变性（@top-invariance-sheaves (3)），$W_1 -> W$ 在 $W$ 的泛点上的纤维是有限平展的。于是由 @passage-to-limit-of-properties (2a)，把 $W$ 换成某个稠密开集，便可设 $pi: W_1 -> W$ 是有限平展覆叠。 

  设 $j: W -> X$ 是开浸入，$i: X - W -> X$ 是补闭浸入，并取带支集截面三角： 
  $
    i_* R i^! cal(F) -> cal(F) -> R j_* j^(-1) cal(F) ->^(+1)
  $
  假定存在 $S$ 的稠密开集，它既是 $(j, j^(-1) cal(F), S)$-好的，又是 $(f compose j, j^(-1) cal(F), S)$-好的。把 $S$ 缩小到这个稠密开集，不妨设 $S$ 是 $(f compose j, j^(-1) cal(F), S)$-好的。特别地 $R j_* j^(-1) cal(F) in D^b_c (X_et, Lambda)$，从而 $i_* R i^! cal(F) in D^b_c (X_et, Lambda)$。于是由 @finite-morphisms-and-constructible-sheaves，$R i^! cal(F) in D^b_c ((X - W)_et, Lambda)$。 
  
  现在 $f compose i: X - W -> Y$ 是有限型 $S$-概形之间的映射。$X_sigma$ 的泛点是 $X$ 中位于 $sigma$ 上方的泛点，它们都落在 $W$ 里，所以 $W_sigma$ 在 $X_sigma$ 中稠密。于是 $dim((X - W)_sigma) < dim(X_sigma) = d$。由归纳假设，存在 $(f compose i, R i^! cal(F), S)$-好的稠密开集 $U subset S$。于是： 
  
  - $U$ 是 $(f, i_* R i^! cal(F), S)$-好的； 

  - $S$ 是 $(j, j^(-1) cal(F), S)$-好的，也是 $(f compose j, j^(-1) cal(F), S)$-好的，从而是 $(f, R j_* j^(-1) cal(F), S)$-好的。 

  利用带支集截面三角便知 $U$ 是 $(f, cal(F), S)$-好的，证毕。于是只剩下证明： 

  - 存在 $S$ 的稠密开集，它既是 $(j, j^(-1) cal(F), S)$-好的，又是 $(f compose j, j^(-1) cal(F), S)$-好的。 

  现在 $j: W -> X$ 与 $f compose j: W -> Y$ 都是支配的开浸入，其中 $dim(W_sigma) <= d$，$W$ 在 $S$ 上光滑，且存在有限平展覆叠 $pi: W_1 -> W$，使 $cal(F)|_(W_1)$ 在每个连通分支上常值。因此只需证明： 

  - 对任意支配的开浸入 $f: X -> Y$ 与 l.c.c. 层 $cal(F) in cAb(X_et, Lambda)$，若 $dim(X_sigma) <= d$、$X$ 在 $S$ 上光滑，且存在有限平展覆叠 $pi: X_1 -> X$ 使 $cal(F)|_(X_1)$ 在每个连通分支上常值，则存在 $S$ 的 $(f, cal(F), S)$-好稠密开集。 

  我们断言可以设 $Y$ 在 $S$ 上紧合，也就是说，只需证明：

  - 对任意支配的开浸入 $f: X -> Y$ 与 l.c.c. 层 $cal(F) in cAb(X_et, Lambda)$，若 $dim(X_sigma) <= d$、$X$ 在 $S$ 上光滑、$Y$ 在 $S$ 上紧合，且存在有限平展覆叠 $pi: X_1 -> X$ 使 $cal(F)|_(X_1)$ 在每个连通分支上常值，则存在 $S$ 的 $(f, cal(F), S)$-好稠密开集。 

  事实上，假定这一情形成立。对一般情形，由在 $Y$ 上的局部性，不妨设 $Y$ 仿射，于是 $Y -> S$ 是有限型的分离态射。取紧化 $Y ->^j ol(Y) -> S$，其中可设 $j$ 支配（换成概形像即可）。现在由紧合情形，把 $S$ 适当缩小，便可设 $S$ 是 $(j compose f, cal(F), S)$-好的。于是： 
    
  - $R j_* R f_* cal(F) in D^b_c (ol(Y)_et, Lambda)$。作用 $j^(-1)$ 便知 $R f_* cal(F) in D^b_c (Y_et, Lambda)$。 

  - 对任意拉回图表：#h(1fr)
    // https://q.uiver.app/#r=typst&q=WzAsOCxbMCwxLCJYIl0sWzEsMSwiWSJdLFsyLDEsIm9sKFkpIl0sWzMsMSwiUyJdLFszLDAsIlMnIl0sWzIsMCwib2woWSknIl0sWzEsMCwiWSJdLFswLDAsIlgiXSxbMCwxLCJmIiwyXSxbMSwyLCJqIiwyXSxbMiwzXSxbNyw2LCJmJyJdLFs2LDUsImonIl0sWzUsNF0sWzQsMywiZyJdLFs1LDIsIm9sKGcpJyJdLFs2LDEsImcnIl0sWzcsMCwiZycnIiwyXV0=
    #align(center, diagram({
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      node((2, 1), [$ol(Y)$])
      node((3, 1), [$S$])
      node((3, 0), [$S'$])
      node((2, 0), [$ol(Y)'$])
      node((1, 0), [$Y$])
      node((0, 0), [$X$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((1, 1), (2, 1), [$j$], label-side: right, "->")
      edge((2, 1), (3, 1), "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (2, 0), [$j'$], label-side: left, "->")
      edge((2, 0), (3, 0), "->")
      edge((3, 0), (3, 1), [$g$], label-side: left, "->")
      edge((2, 0), (2, 1), [$ol(g)'$], label-side: left, "->")
      edge((1, 0), (1, 1), [$g'$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g''$], label-side: right, "->")
    }))
    有： 
    $
      ol(g)'^(-1) R j_* R f_* cal(F) cong R j'_* R f'_* g''^(-1) cal(F)
    $
    作用 $j'^(-1)$，得到： 
    $
      j'^(-1) ol(g)'^(-1) R j_* R f_* cal(F) cong g'^(-1) j^(-1) R j_* R f_* cal(F) cong g'^(-1) R f_* cal(F)
    $
    而 $j'^(-1) R j'_* R f'_* g''^(-1) cal(F) cong R f'_* g''^(-1) cal(F)$。于是我们得到了同构 $ol(g)'^(-1) R j_* R f_* cal(F) cong g'^(-1) R f_* cal(F)$，由自然性可以验证它就是基变换映射。故 $S$ 是 $(f, cal(F), S)$-好的。 

  于是还可额外设 $Y$ 在 $S$ 上紧合。为继续归纳，我们需要下面的引理： 
  
  #lemma[
    设 $f: X -> Y$ 是有限型 $S$-概形之间的支配开浸入，且 $dim(X_sigma) <= d$；取 $cal(K) in D^b_c (X_et, Lambda)$。则把 $S$ 缩小到某个稠密开集后，存在开子集 $V subset Y$，使得： 

    - $Y - V -> S$ 有限； 

    - $S$ 是 $(f_V, cal(K)|_(X_V), S)$-好的，其中 $f_V: X_V -> V$ 是 $f$ 到 $V$ 的基变换。 
  ]
  #proof[
    暂且设 $Y$ 仿射。由于 $Y -> S$ 是仿射概形之间的有限型态射，可以取闭浸入 $i: Y -> AA^m_S$（任取 $cal(O)_Y (Y)$ 作为 $cal(O)_S (S)$-代数的一个有限展示即可）。设 $pi_j: AA^m_S -> AA^1_S, 1<=j<=m$ 是到各坐标的投影。再考虑 $g_j = pi_j compose i compose f: X -> AA^1_S$。任取 $x in X_sigma$，并设 $K = K(S)$ 是 $S$ 的函数域。则： 
    $
      trd_(K) (k(x)) <= dim(X_sigma) <= d
    $
    设 $tau = Spec(K(t))$ 是 $AA^1_S$ 的泛点。若 $x in g_j^(-1) (tau)$，则： 
    $
      trd_(K(t)) (k(x)) = trd_K (k(x)) - trd_K (K(t)) <= d - 1
    $
    于是 $g_j$ 的泛纤维维数满足 $dim(g_j^(-1) (tau)) <= d-1$。从而可以对 $g_j$ 应用归纳假设，得到：
    
    - 对每个 $j$，存在 $(i_j compose f_j, cal(K), AA^1_S)$-好稠密开集 $U_j subset AA^1_S$。 

      置 $V_j = i^(-1) (pi_j^(-1) (U_j)) subset Y$，并把 $X ->^f Y ->^i AA^m_S ->^(pi_j) AA^1_S$ 沿 $U_j -> AA^1_S$ 作基变换，得到：#h(1fr)
      $
        X_j ->^(f_j) V_j ->^(i_j) AA^(m-1)_(U_j) ->^(tilde(pi)_j) U_j
      $

      则： 
      $
        i_(j,*) R f_(j,*) (cal(K)|_(X_j)) in D^b_c ((U_j)_et, Lambda)
      $
      由 @finite-morphisms-and-constructible-sheaves，$R f_(j,*) (cal(K)|_(X_j)) in D^b_c ((V_j)_et, Lambda)$。进一步，对任意 $g: S' -> S$，作拉回图表： 
      // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMSwiWF9qIl0sWzEsMSwiVl9qIl0sWzIsMSwicGlfal4oLTEpIChVX2opIl0sWzMsMSwiVV9qIl0sWzQsMSwiUyJdLFs0LDAsIlMnIl0sWzMsMCwiVSdfaiJdLFsyLDAsInBpJ19qIChVJ19qKSJdLFsxLDAsIlYnX2oiXSxbMCwwLCJYJ19qIl0sWzUsNCwiZyJdLFs2LDMsImcnX2oiXSxbNywyLCJnJydfaiJdLFs4LDEsImdfKFZfaikiXSxbOSwwLCJnXyhYX2opIiwyXSxbMCwxLCJmX2oiLDJdLFsxLDIsImkiLDJdLFsyLDMsInBpX2oiLDJdLFszLDRdLFs5LDgsImYnX2oiXSxbOCw3LCJpJyJdLFs3LDYsInBpJ19qIl0sWzYsNV1d
      #align(center, diagram({
        node((0, 1), [$X_j$])
        node((1, 1), [$V_j$])
        node((2, 1), [$pi_j^(-1) (U_j)$])
        node((3, 1), [$U_j$])
        node((4, 1), [$S$])
        node((4, 0), [$S'$])
        node((3, 0), [$U'_j$])
        node((2, 0), [$pi'_j (U'_j)$])
        node((1, 0), [$V'_j$])
        node((0, 0), [$X'_j$])
        edge((4, 0), (4, 1), [$g$], label-side: left, "->")
        edge((3, 0), (3, 1), [$g'_j$], label-side: left, "->")
        edge((2, 0), (2, 1), [$g''_j$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g_(V_j)$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g_(X_j)$], label-side: right, "->")
        edge((0, 1), (1, 1), [$f_j$], label-side: right, "->")
        edge((1, 1), (2, 1), [$i$], label-side: right, "->")
        edge((2, 1), (3, 1), [$pi_j$], label-side: right, "->")
        edge((3, 1), (4, 1), "->")
        edge((0, 0), (1, 0), [$f'_j$], label-side: left, "->")
        edge((1, 0), (2, 0), [$i'$], label-side: left, "->")
        edge((2, 0), (3, 0), [$pi'_j$], label-side: left, "->")
        edge((3, 0), (4, 0), "->")
      }))
      则 $g''_j$ 是态射 $g'_j: U'_j -> U_j$ 的基变换，于是由 $U_j$ 的 $(f_j, cal(K)|_(X_j), AA^1_S)$-好性，得到基变换同构：
      $
        g''_j^(-1) i_* R f_(j,*) (cal(K)|_(X_j)) cong i'_* R f'_(j,*) g_(X_j)^(-1) (cal(K)|_(X_j))
      $
      现在基变换映射 $g''_j^(-1) i_* -> i'_* g_(V_j)^(-1)$ 是同构，于是得到同构： 
      $
        i'_* g_(V_j)^(-1) R f_(j,*) (cal(K)|_(X_j)) -> i'_* R f'_(j,*) g_(X_j)^(-1) (cal(K)|_(X_j))
      $
      再作用 $i'^(-1)$，便知基变换 $g_(V_j)^(-1) R f_(j,*) (cal(K)|_(X_j)) -> R f'_(j,*) g_(X_j)^(-1) (cal(K)|_(X_j))$ 是同构。这就是说 $S$ 是 $(f_j, cal(K)|_(X_j), S)$-好的。 

    - 现在置： 
      $
        V = union.big_(j=1)^m V_j
      $
      并设 $f_V: X_V -> V$ 是 $f$ 到 $V$ 的基变换。 

      由于对每个 $j$，$S$ 都是 $(f_j, cal(K)|_(X_j), S)$-好的，可知 $S$ 是 $(f_V, cal(K)|_(X_V), S)$-好的。此外： 
      $
        Y - V &= Y - i^(-1) (union.big_(j=1)^m pi_j^(-1) (U_j)) \
        &= i^(-1) (AA^m_S - union.big_(j=1)^m pi_j^(-1) (U_j)) #[因为 $i$ 是浸入] \
        &= i^(-1)((AA^1_S - U_1) times_S dots.c times_S (AA^1_S - U_m)) subset Y
      $
      对每个 $j$，泛点 $tau in AA^1_S$ 都落在 $U_j$ 中，故泛纤维 $(U_j)_sigma in AA^1_K$ 包含 $AA^1_K$ 的泛点。于是它的补集是有限多个闭点组成的集合。换言之，把 $AA^1_S - U_j -> AA^1_S -> S$ 基变换到泛点 $sigma in S$ 后是有限的。由 @passage-to-limit-of-properties (2a)，把 $S$ 换成某个稠密仿射开集，便可设 $AA^1_S - U_j -> S$ 有限。因此把 $S$ 缩小到稠密仿射开集、有限多次之后，不妨设对一切 $j$，$AA^1_S - U_j -> S$ 都有限。再由上面的公式，$Y - V$ 在 $S$ 上有限。 

    $Y$ 仿射的情形至此完成。对一般情形，用有限多个仿射开集 ${Y_i}$ 覆盖 $Y$，并基变换到 $f_i: X_i -> Y_i$。此时对每个 $Y_i$，存在开集 $V_i subset Y_i$，使得： 

    - $S$ 是 $(f_(V_i), cal(K)|_(X_(V_i)), S)$-好的； 

    - $Y_i - V_i -> S$ 有限。 

    置 $V = union.big_i V_i$。现在： 

    - $Y_sigma - V_sigma = union.big_i ((Y_i)_sigma - (V_i)_sigma)$ 是有限集，因为每个 $Y_i - V_i -> S$ 都有限。于是由 @passage-to-limit-of-properties (2a)，缩小 $S$ 便可设 $Y - V -> S$ 有限； 

    - 局部检查可知 $S$ 是 $(f_V, cal(K)|_(X_V), S)$-好的。 

    至此完成。 
  ]

  现在设： 

  - $f: X -> Y$ 是有限型 $S$-概形之间的支配开浸入，其中 $X$ 在 $S$ 上光滑、$dim(X_sigma) <= d$，且 $Y$ 在 $S$ 上紧合。 

  - $cal(F) in cAb(X_et, Lambda)$ 是 l.c.c. $Lambda$-模层，且存在有限平展覆叠 $pi: X_1 -> X$，使 $cal(F)|_(X_1)$ 在 $X_1$ 的每个连通分支上常值。 

  我们要证明存在 $S$ 的 $(f, cal(F), S)$-好稠密开集。由上一条引理，取开集 $V subset Y$，配以互补的浸入 $j: V -> Y, i: W = Y - V -> Y$。作交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNixbMCwxLCJYIl0sWzEsMSwiWSJdLFsxLDAsIlYiXSxbMSwyLCJTIl0sWzIsMSwiVi1ZIl0sWzAsMCwiWF9WIl0sWzIsMSwiaiJdLFs0LDEsImkiLDJdLFswLDEsImYiXSxbMCwzLCJhIiwyXSxbMSwzLCJiIiwxXSxbNCwzLCJjIl0sWzUsMiwiZl9WIl0sWzUsMCwiaiciLDJdXQ==
  #context align(center, diagram({
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    node((1, 0), [$V$])
    node((1, 2), [$S$])
    node((2, 1), [$W = Y-V$])
    node((0, 0), [$X_V$])
    edge((1, 0), (1, 1), [$j$], label-side: left, "->")
    edge((2, 1), (1, 1), [$i$], label-side: right, "->")
    edge((0, 1), (1, 1), [$f$], label-side: left, "->")
    edge((0, 1), (1, 2), [$a$], label-side: right, "->")
    edge((1, 1), (1, 2), [$b$], label-side: center, "->")
    edge((2, 1), (1, 2), [$c$], label-side: left, "->")
    edge((0, 0), (1, 0), [$f_V$], label-side: left, "->")
    edge((0, 0), (0, 1), [$j_X$], label-side: right, "->")
  }, crossing-fill: thm-box-curr-color()))
  其左上角方块是拉回。于是由我们的假设与 $V$ 的选取，把 $S$ 适当缩小为仿射开集后： 

  - $a$ 光滑，$b$ 紧合，$c$ 有限； 

  - $S$ 是 $(f_V, cal(F)|_(X_V), S)$-好的。 

  我们在下述额外假设下证明存在 $S$ 的 $(f, cal(F), S)$-好稠密开集： 

  - 存在 $S$ 的稠密开集，它是 $(a, cal(F), S)$-好的。 

  缩小 $S$，不妨设 $S$ 是 $(a, cal(F), S)$-好的。考虑零延拓三角： 
  $
    underbrace(j_! j^(-1) R f_* cal(F), j_! R f_(V,*) (cal(F)|_(X_V))) -> R f_* cal(F) -> i_* i^(-1) R f_* cal(F) ->^(+1)
  $
  对它作用 $R b_*$，得到特殊三角： 
  $
    R b_* j_! R f_(V,*) (cal(F)|_(X_V)) -> R a_* cal(F) -> c_* i^(-1) R f_* cal(F) ->^(+1)
  $
  现在： 

  - 由于 $S$ 是 $(a, cal(F), S)$-好的，有 $R a_* cal(F) in D^b_c (S_et, Lambda)$。 

    由于 $S$ 是 $(f_V, cal(F)|_(X_V), S)$-好的，有 $R f_(V,*) (cal(F)|_(X_V)) in D^b_c (V_et, Lambda)$。又 $b$ 紧合，故由 $R(b compose j)_!$ 的有限性（据 @finiteness-of-lower-shriek），$R b_* j_! R f_(V,*) (cal(F)|_(X_V)) in D^b_c (S_et, Lambda)$。 

    于是由这个特殊三角，$c_* i^(-1) R f_* cal(F) in D^b_c (S_et, Lambda)$。由 @finite-morphisms-and-constructible-sheaves，$i^(-1) R f_* cal(F) in D^b_c (W_et, Lambda)$，从而 $i_* R f_* cal(F) in D^b_c (Y_et, Lambda)$。另一方面 $j_! j^(-1) R f_* cal(F) = j_! R f_(V,*) (cal(F)|_(X_V)) in D^b_c (Y_et, Lambda)$，故由零延拓三角： 
    $
      R f_* cal(F) in D^b_c (Y_et, Lambda)
    $

  - 对任意 $g: S' -> S$，沿 $g$ 把图表基变换为： 
    // https://q.uiver.app/#r=typst&q=WzAsMTIsWzEsNSwiWCJdLFszLDQsIlkiXSxbNSwzLCJXIl0sWzIsMywiViJdLFswLDQsIlhfViJdLFs0LDUsIlMiXSxbMSwyLCJYJyJdLFs0LDIsIlMnIl0sWzIsMCwiViciXSxbMywxLCJZJyJdLFswLDEsIlhfKFYnKSJdLFs1LDAsIlcnIl0sWzAsMSwiZiIsMV0sWzIsMSwiaSIsMV0sWzMsMSwiaiIsMV0sWzQsMywiZl9WIiwxXSxbNCwwLCJqX1giLDFdLFswLDUsImEiLDFdLFsxLDUsImIiLDFdLFsyLDUsImMiLDFdLFs2LDksImYnIiwxXSxbMTEsOSwiaSciLDFdLFs4LDksImonIiwxXSxbMTAsOCwiZidfViIsMV0sWzEwLDYsImonX1giLDFdLFs2LDcsImEnIiwxXSxbOSw3LCJiJyIsMV0sWzExLDcsImMnIiwxXSxbMTAsNCwiZ18oWF9WKSIsMV0sWzYsMCwiZ19YIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzgsMywiZ19WIiwxLHsibGFiZWxfcG9zaXRpb24iOjgwfV0sWzksMSwiZ19ZIiwxXSxbNyw1LCJnIiwxLHsibGFiZWxfcG9zaXRpb24iOjIwfV0sWzExLDIsImdfVyIsMSx7ImxhYmVsX3Bvc2l0aW9uIjo4MH1dXQ==
    #context align(center, diagram({
      node((0, 1), [$X$])
      node((2, 0), [$Y$])
      node((4, -1), [$W$])
      node((1, -1), [$V$])
      node((-1, 0), [$X_V$])
      node((3, 1), [$S$])
      node((0, -2), [$X'$])
      node((3, -2), [$S'$])
      node((1, -4), [$V'$])
      node((2, -3), [$Y'$])
      node((-1, -3), [$X'_(V)$])
      node((4, -4), [$W'$])
      edge((0, 1), (2, 0), [$f$], label-side: center, "->")
      edge((4, -1), (2, 0), [$i$], label-side: center, "->", layer: 1, label-pos: 0.7)
      edge((1, -1), (2, 0), [$j$], label-side: center, "->")
      edge((-1, 0), (1, -1), [$f_V$], label-side: center, "->", layer: 1, label-pos: 0.7)
      edge((-1, 0), (0, 1), [$j_X$], label-side: center, "->")
      edge((0, 1), (3, 1), [$a$], label-side: center, "->")
      edge((2, 0), (3, 1), [$b$], label-side: center, "->")
      edge((4, -1), (3, 1), [$c$], label-side: center, "->")
      edge((0, -2), (2, -3), [$f'$], label-side: center, "->", layer: 1, label-pos: 0.7)
      edge((4, -4), (2, -3), [$i'$], label-side: center, "->")
      edge((1, -4), (2, -3), [$j'$], label-side: center, "->")
      edge((-1, -3), (1, -4), [$f'_V$], label-side: center, "->")
      edge((-1, -3), (0, -2), [$j'_X$], label-side: center, "->")
      edge((0, -2), (3, -2), [$a'$], label-side: center, "->")
      edge((2, -3), (3, -2), [$b'$], label-side: center, "->")
      edge((4, -4), (3, -2), [$c'$], label-side: center, "->")
      edge((-1, -3), (-1, 0), [$g_(X_V)$], label-side: center, "->")
      edge((0, -2), (0, 1), [$g_X$], label-side: center, label-pos: 0.15, "->")
      edge((1, -4), (1, -1), [$g_V$], label-side: center, label-pos: 0.85, "->")
      edge((2, -3), (2, 0), [$g_Y$], label-side: center, "->")
      edge((3, -2), (3, 1), [$g$], label-side: center, label-pos: 0.15, "->")
      edge((4, -4), (4, -1), [$g_W$], label-side: center, label-pos: 0.85, "->")
    }, crossing-fill: thm-box-curr-color(), spacing: 2em))
    
    我们要证明基变换 $g_Y^(-1) R f_* cal(F) -> R f'_* g_X^(-1) cal(F)$ 是同构。置 $cal(F)' = cal(F)|_(X')$。考虑特殊三角： 
    $
      R b_* j_! R f_(V,*) (cal(F)|_(X_V)) -> R a_* cal(F) -> c_* i^(-1) R f_* cal(F) ->^(+1)
    $
    以及对基变换后映射的同一个三角： 
    $
      R b'_* j'_! R f'_(V,*) (cal(F)'|_(X_V)) -> R a'_* cal(F)' -> c'_* i'^(-1) R f'_* cal(F)' ->^(+1)
    $
    现在对第一个三角作用 $g^(-1)$： 

    - 由于 $S$ 是 $(a, cal(F), S)$-好的，基变换 $g^(-1) R a_* cal(F) -> R a'_* cal(F)'$ 是同构； 

    - 对第一项：#h(1fr)
      $
        g^(-1) R b_* j_! R f_(V,*) (cal(F)|_(X_V)) &cong R b'_* j'_! g_V^(-1) R f_(V,*) (cal(F)|_(X_V)) #[由紧合基变换] \
        &cong R b'_* j'_! R f'_(V,*) (cal(F')|_(X'_V)) #[因为 $S$ 是 $(f_V, cal(F)|_(X_V), S) $-好的] 
      $
    
    于是利用这两个特殊三角，既然第一项与第二项上的基变换映射是同构，第三项上的基变换映射也必定是同构。也就是说，基变换映射： 
    $
      g^(-1) c_* i^(-1) R f_* cal(F) -> c'_* i'^(-1) R f'_* cal(F)'
    $
    是同构。现在 $c$ 有限，故 $g^(-1) c_* cong c'_* g_W^(-1)$。换言之， 
    $
      c'_* g_W^(-1) i^(-1) R f_* cal(F) -> c'_* i'^(-1) R f'_* cal(F)'
    $ 
    是同构。现在 $c'$ 有限，故逐茎检查可知 $g_W^(-1) i^(-1) R f_* cal(F) -> i'^(-1) R f'_* cal(F)'$ 是同构。作用 $i'_*$，再利用 $i_*$ 的基变换，便知基变换： 
    $
      g_Y^(-1) i_* i^(-1) R f_* cal(F) -> i'_* i'^(-1) R f'_* cal(F)'
    $
    是同构。 

    此外，我们已经看到： 
    $
      g_Y^(-1) j_! R f_(V,*) (cal(F)|_(X_V)) cong j'_! g_V^(-1) R f_(V,*) (cal(F)|_(X_V)) cong j'_! R f'_(V,*) (cal(F)'|_(X'_V))
    $
    这里用到 $S$ 是 $(f_V, cal(F)|_(X_V), S)$-好的。现在取零延拓三角： 
    $
      j_! R f_(V,*) (cal(F)|_(X_V)) -> R f_* cal(F) -> i_* i^(-1) R f_* cal(F) ->^(+1)
    $
    以及： 
    $
      j'_! R f'_(V,*) (cal(F)'|_(X'_V)) -> R f'_* cal(F)' -> i'_* i'^(-1) R f'_* cal(F)' ->^(+1)
    $
    对第一个三角作用 $g_Y^(-1)$，就得到它到第二个三角的基变换映射；我们已证明它在第一、第三位置上是同构。于是它在第二个位置上也是同构，即： 
    $
      g_Y^(-1) R f_* cal(F) cong R f'_* cal(F)'
    $
    该同构由基变换给出。 

  这两段论证合起来表明 $S$ 是 $(f, cal(F), S)$-好的，证毕。剩下唯一要证的假设是：把 $S$ 适当缩小后，$S$ 是 $(a, cal(F), S)$-好的。换言之，还需证明： 

  - 若 $f: X -> S$ 是分离的光滑态射，$cal(F) in cAb(X_et, Lambda)$ 是被有限平展覆叠 $pi: X_1 -> X$ 平凡化的 l.c.c. $Lambda$-模层，则存在 $S$ 的 $(f, cal(F), S)$-好稠密开集。 

  对 $X$ 的每个连通分支分别处理，不妨设 $X$ 连通。此时 $X_1$ 的任一连通分支都满射到 $X$，故也可设 $X_1$ 满射。取 Galois 闭包，还可设 $pi: X_1 -> X$ 是 Galois 覆叠。由于假定 $X$ 连通，光滑映射 $X -> S$ 有某个纯相对维数 $d$（即 $X$ 上局部自由凝聚层 $Omega_(X\/S)$ 的秩）。 

  利用滤过 $0 -> ell cal(F) -> cal(F) -> cal(F)\/ell cal(F) -> 0$，只需证明 $cal(F)$ 为 $ell$-挠的情形，其中 $ell in cal(O)_S^times$ 是素数。再把 $Lambda$ 换成 $Lambda\/ell Lambda$，不妨设 $Lambda$ 也是 $ell$-挠的。现在由 @finiteness-of-lower-shriek，$R f_! ul(ZZ\/ell) in D^b_c (S_et, Lambda)$。于是缩小 $S$，还可设： 

  - 每个 $R^q f_(1,!) ul(ZZ\/ell)$ 都是 l.c.c. 的 $ZZ\/ell$-模层。 

  我们断言：此时 $S$ 是 $(f_1, ul(ZZ\/ell), S)$-好的，且每个 $R^q f_* ul(ZZ\/ell)$ 都是 l.c.c.。 

  #proof_[断言的证明][
    把 $f$ 换成 $f_1$，便可设每个 $R^q f_! ul(ZZ\/ell)$ 都是 l.c.c.。此时 $f$ 仍是相对维数为 $d$ 的光滑态射。 

    由 Poincaré 对偶（@relative-poincare-duality），有典范同构 $R f^! ul(ZZ\/ell) cong ul(ZZ\/ell)(d)[2d]$。于是由内伴随得到典范同构： 
    $
      R f_* ul(ZZ\/ell)(d)[2d] cong R f_* RHHom_(ZZ\/ell) (ul(ZZ\/ell), ul(ZZ\/ell)(d)[2d]) cong RHHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell))
    $
    即典范同构： 
    $
      R f_* ul(ZZ\/ell) cong RHHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell))(-d)[-2d]
    $

    - 注意 $RHHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell)) = HHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell))$。事实上，对单个 l.c.c. 的 $ul(ZZ\/ell)$-模层 $cal(G)$，由 @lcc-and-injective-has-no-higher-ext 有 $RHHom_(ZZ\/ell) (cal(G), ul(ZZ\/ell)) = HHom_(ZZ\/ell) (cal(G), ul(ZZ\/ell))$。于是利用截断得到： 
      $
        RHHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell)) = HHom_(ZZ\/ell) (R f_! ul(ZZ\/ell), ul(ZZ\/ell))
      $
      逐次粘合各个次数即得。 

    因此有典范同构： 
    $
      R^q f_* ul(ZZ\/ell) cong HHom_(ZZ\/ell)(R^(2d-q) f_! ul(ZZ\/ell), ul(ZZ\/ell)) (-d)
    $
    于是 $R^q f_* ul(ZZ\/ell)$ 在 $0<=q<=2d$ 之外消没；并且它是 l.c.c. 的（因为 $R^(2d-q) f_! ul(ZZ\/ell)$ 是 l.c.c.，故任何平凡化 $R^(2d-q) f_! ul(ZZ\/ell)$ 的平展覆盖也平凡化 $R^q f_* ul(ZZ\/ell)$）。进一步，对任意 $g: S' -> S$，典范映射 $g^(-1) HHom_(ZZ\/ell) (R^(2d-q) f_! ul(ZZ\/ell), ul(ZZ\/ell)) -> HHom_(ZZ\/ell) (g^(-1) R^(2d-q) f_! ul(ZZ\/ell), ul(ZZ\/ell))$ 是同构。（一般情形下这并不成立，但此处可以沿平凡化的平展覆盖拉回检查：拉回后一切都常值，再用 @surjective-pullback-conservative 即可。）于是基变换映射： 
    $
      g^(-1) R f_* ul(ZZ\/ell) -> R f'_* ul(ZZ\/ell)
    $
    由下述基变换映射诱导： 
    $
      g^(-1) R f_! ul(ZZ\/ell) -> R f'_! ul(ZZ\/ell)
    $
    由紧合基变换，它是同构。因此 $R f_* ul(ZZ\/ell)$ 的构造与基变换相容。也就是说，我们证明了 $S$ 是 $(f, ul(ZZ\/ell), S)$-好的。 
  ]
  现在令 $f_1: X_1 ->^pi X -> S$，并设 $pi^(-1) cal(F) = ul(M)$，其中 $M$ 是有限 $Lambda$-模。则有一个投影映射（这里因为 $ZZ\/ell$ 是域，张量积正合，不需要取左导出）： 
  $
    R f_(1,*) pi^(-1) cal(F) = R f_(1,*) (ul(ZZ\/ell) otimes_(ZZ\/ell) ul(M)) -> R f_(1,*) ul(ZZ\/ell) otimes_(ZZ\/ell) ul(M)
  $
  这个投影映射是同构。/*事实上，取一组基便可设 $ul(M) = ul(ZZ\/ell)^(oplus I)$。于是由 @limit-formula-for-sheaves， 
  $
    R^q f_(1,*) ul(M) cong (R^q f_(1,*) ul(ZZ\/ell))^(oplus I) cong R^q f_(1,*) ul(ZZ\/ell) otimes_(ZZ\/ell) ul(M)
  $*/事实上，$id$ 相对 $ul(M)$ 是泛局部零调的（比如由 @loc-acyc-of-smooth-maps），所求的投影同构便由 @loc-acyc-and-base-change 推出。 


  然而，$R^q f_(1,*) ul(ZZ\/ell)$ 都是 l.c.c. 的 $ul(ZZ\/ell)$-模层。因此 $R^q f_(1,*) ul(M)$ 是 l.c.c. 的 $Lambda$-模层，而且，凡在 $S$ 上平凡化 $R^q f_(1,*) ul(ZZ\/ell)$ 的有限平展覆叠，也都平凡化它。$R^q f_(1,*) ul(ZZ\/ell)$ 的基变换相容性同样传给 $R^q f_(1,*) ul(M)$。于是我们得到： 

  - $S$ 是 $(f_1, ul(M), S)$-好的，且 $R^q f_(1,*) ul(M) = R^q f_* pi_* pi^(-1) cal(F)$ 都是 l.c.c. 的 $Lambda$-模层。 

  也就是说，把结论完整地写成自足的表述： 
  
  - 设 $f: X -> S$ 是纯相对维数的分离光滑态射，$X$ 连通；$Lambda$ 是对某个素数 $ell$ 而言的 $ell$-挠 Noether 环。又设给定 Galois 平展覆叠空间 $pi: X_1 -> X$，并令 $f_1: X_1 ->^pi X -> S$。 
  
    则把 $S$ 缩小、使每个 $R^q f_(1,!) ul(ZZ\/ell)$ 都成为 l.c.c. 之后，对任意被 $pi$ 平凡化的 l.c.c. $Lambda$-模层 $cal(F) in cAb(X_et, Lambda)$，$S$ 都是 $(f_1, pi^(-1) cal(F), S)$-好的。 

  要继续推进，本质上需要对群 $Aut(X_1\/X)$ 在平展层上作某种群上同调。我不愿意为此写一长串构造，于是换成了一个你已见过多次的粗糙四引理归纳。 

  取正合列： 
  $
    0 -> cal(F) -> pi_* pi^(-1) cal(F) -> cal(R) -> 0
  $
  现在 $cal(F)$ 与 $pi_* pi^(-1) cal(F)$ 都是被 $pi$ 平凡化的 l.c.c. $Lambda$-模层，故 $cal(R)$ 也是。记： 

  - $T(q)$ 为下述命题：对 $X$ 上每个被 $pi$ 平凡化的 l.c.c. $Lambda$-模层 $cal(F)$：
  
    - 对一切 $p<=q$，$R^p f_* cal(F)$ 可构造； 
    
    - 对每个拉回图表：#h(1fr)
      #align(center, diagram({
        node((0, 0), [$X'$])
        node((1, 0), [$S'$])
        node((0, 1), [$X$])
        node((1, 1), [$S$])
        node((0.3, 0.3), [$cart$])
        edge((0, 1), (1, 1), [$f$], label-side: right, "->")
        edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
        edge((1, 0), (1, 1), [$g$], label-side: left, "->")
        edge((0, 0), (0, 1), [$g'$], label-side: right, "->")
      }))
      基变换 $g^(-1) R^p f_* cal(F) -> R^p f'_* g'^(-1) cal(F)$ 对每个 $0<=p<=q$ 都是同构。 
    

  - $T'(q)$ 为命题 $T(q)$，但只要求当 $p=q$ 时 $g^(-1) R^p f_* cal(F) -> R^p f'_* g'^(-1) cal(F)$ 是单射。 

  假定 $T(q-1)$ 成立。任取被 $pi$ 平凡化的 l.c.c. 层 $cal(F) in cAb(X_et, Lambda)$。现在： 

  - 有长正合列 $dots.c -> R^(q-1) f_* cal(R) -> R^q f_* cal(F) -> R^q f_(1,*) pi^(-1) cal(F) -> dots.c$。由 $T(q-1)$ 与前面的论证，$R^q f_* cal(F)$ 被夹在两个可构造层之间，故可构造。 

  - 任取 $g: S' -> S$，作通常的拉回图表。现在考虑行正合的交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsMTQsWzAsMCwiZG90cy5jIl0sWzAsMSwiZG90cy5jIl0sWzEsMCwiZ14oLTEpIFJeKHEtMSkgZl8oMSwqKSBwaV4oLTEpIGNhbChGKSJdLFsyLDAsImdeKC0xKSBSXihxLTEpIGZfKiBjYWwoUikiXSxbMywwLCJnXigtMSkgUl5xIGZfKiBjYWwoRikiXSxbNCwwLCJnXigtMSkgUl5xIGZfKDEsKikgcGleKC0xKSBjYWwoRikiXSxbNSwwLCJnXigtMSkgUl5xIGZfKiBjYWwoUikiXSxbNiwwLCJkb3RzLmMiXSxbMSwxLCJSXihxLTEpIGYnXygxLCopIHBpJ14oLTEpIGcnXigtMSkgY2FsKEYpIl0sWzQsMSwiUl5xIGYnXygxLCopIHBpJ14oLTEpIGcnXigtMSkgY2FsKEYpIl0sWzIsMSwiUl4ocS0xKSBmJ18qIGcnXigtMSkgY2FsKFIpIl0sWzUsMSwiUl5xIGYnXyogZydeKC0xKSBjYWwoUikiXSxbMywxLCJSXnEgZidfKiBnJ14oLTEpIGNhbChGKSJdLFs2LDEsImRvdHMuYyJdLFswLDJdLFsyLDNdLFszLDRdLFs0LDVdLFs1LDZdLFs2LDddLFsxLDhdLFs4LDEwXSxbMTAsMTJdLFsxMiw5XSxbOSwxMV0sWzExLDEzXSxbMiw4XSxbMywxMF0sWzQsMTJdLFs1LDldLFs2LDExXV0=
    #align(center, diagram({
      node((0, 0), [$dots.c$])
      node((0, 1), [$dots.c$])
      node((1, 0), [$g^(-1) R^(q-1) f_(1,*) pi^(-1) cal(F)$])
      node((2, 0), [$g^(-1) R^(q-1) f_* cal(R)$])
      node((3, 0), [$g^(-1) R^q f_* cal(F)$])
      node((4, 0), [$g^(-1) R^q f_(1,*) pi^(-1) cal(F)$])
      node((5, 0), [$g^(-1) R^q f_* cal(R)$])
      node((6, 0), [$dots.c$])
      node((1, 1), [$R^(q-1) f'_(1,*) pi'^(-1) g'^(-1) cal(F)$])
      node((4, 1), [$R^q f'_(1,*) pi'^(-1) g'^(-1) cal(F)$])
      node((2, 1), [$R^(q-1) f'_* g'^(-1) cal(R)$])
      node((5, 1), [$R^q f'_* g'^(-1) cal(R)$])
      node((3, 1), [$R^q f'_* g'^(-1) cal(F)$])
      node((6, 1), [$dots.c$])
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0), "->")
      edge((2, 0), (3, 0), "->")
      edge((3, 0), (4, 0), "->")
      edge((4, 0), (5, 0), "->")
      edge((5, 0), (6, 0), "->")
      edge((0, 1), (1, 1), "->")
      edge((1, 1), (2, 1), "->")
      edge((2, 1), (3, 1), "->")
      edge((3, 1), (4, 1), "->")
      edge((4, 1), (5, 1), "->")
      edge((5, 1), (6, 1), "->")
      edge((1, 0), (1, 1), "->")
      edge((2, 0), (2, 1), "->")
      edge((3, 0), (3, 1), "->")
      edge((4, 0), (4, 1), "->")
      edge((5, 0), (5, 1), "->")
    }, spacing: 1.3em, label-size: 0.7em))

    由 $T(q-1)$，前两个竖直箭头是双射。由前面的论证，第四个竖直箭头是双射。 

    - 由单射四引理，第三个箭头是单射。由于 $cal(F)$ 任意，这就证明了 $T'(q)$； 

    - 由 $T'(q)$，第五个箭头是单射。再由满射四引理，第三个箭头是双射。由于 $cal(F)$ 任意，这就证明了 $T(q)$。 

  现在从 $T(-1)$ 出发作归纳，便验证了所有 $T(q)$。再设 $f$ 的纤维维数 $<=d$。则对任意被 $pi$ 平凡化的 l.c.c. 层 $cal(F) in cAb(X_et, Lambda)$ 与任意 $s in S$，由与基变换的相容性， 
  $
    s^(-1) R^q f_* cal(F) = R^q f_(s,*) s^(-1) cal(F) = 0 
  $
  只要 $q > 2dim(X_s)$（这里用到 @relative-artin-grothendieck-vanishing (2)）。此时对 $s$ 上方的任意几何点 $ol(s)$，有 $(R^q f_* cal(F))_(ol(s)) = 0$。于是若取 $q > 2d$，则对 $S$ 的每个几何点 $ol(s)$ 都有 $(R^q f_* cal(F))_(ol(s)) = 0$，从而 $R^q f_* cal(F) = 0$。 

  总结上面的讨论，可得： 

  - 设 $f: X -> S$ 是纯相对维数的分离光滑态射，$X$ 连通；$Lambda$ 是对某个素数 $ell$ 而言的 $ell$-挠 Noether 环。又设给定 Galois 平展覆叠空间 $pi: X_1 -> X$，并令 $f_1: X_1 ->^pi X -> S$。 
  
    则把 $S$ 缩小、使每个 $R^q f_(1,!) ul(ZZ\/ell)$ 都成为 l.c.c. 之后，对任意被 $pi$ 平凡化的 l.c.c. $Lambda$-模层 $cal(F) in cAb(X_et, Lambda)$，$S$ 都是 $(f, cal(F), S)$-好的。 

  证明至此结束。 
]

一般基变换定理有着深刻的应用。 

#corollary(name: <finiteness-of-rf-lower-star>)[
  ($R f_*$ 的有限性) 设 $k$ 是任意域，$f: X -> Y$ 是有限型 $k$-概形之间的态射，$Lambda$ 是 $n$-挠 Noether 环且 $n in k^times$。则： 
  
  + （有限性）$R f_*: D(X_et, Lambda) -> D(Y_et, Lambda)$ 的上同调维数有上界，并把 $D^b_c (X_et, Lambda)$ 送到 $D^b_c (Y_et, Lambda)$。 

  + （基变换）对任意拉回图表：#h(1fr)
    #align(center, diagram({
      node((0, 0), [$X'$])
      node((1, 0), [$Y'$])
      node((0, 1), [$X$])
      node((1, 1), [$Y$])
      // node((0.3, 0.3), [$cart$])
      node((2, 1), [$Spec(k)$])
      node((2, 0), [$S'$])
      edge((0, 1), (1, 1), [$f$], label-side: right, "->")
      edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
      edge((1, 0), (2, 0), "->")
      edge((1, 1), (2, 1), "->")
      edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
      edge((2, 0), (2, 1), [$g$], label-side: left, "->")
      edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
    }))
    $
      g_Y^(-1) R f_* cal(K) -> R f'_* g_X^(-1) cal(K)
    $
    对一切 $cal(K) in D^b_c (X_et, Lambda)$ 都是同构。 

  // + 设置如 (2)，并假设每个有限 $Lambda$-模都能单射进入某个有限自由 $Lambda$-模。再作一个假设。则对一切 $cal(K) in D^b_c (X_et, Lambda), cal(L) in D^b_#[ctf] (S'_et, Lambda)$，相对基变换有同构： 
  //   $
  //     g_Y^(-1) R f_* cal(K) Lotimes_Lambda cal(L)|_(Y') -> R f'_* (g_X^(-1) cal(K) Lotimes_Lambda cal(L)|_(X'))
  //   $
]
#proof[
  $R f_*$ 的有限上同调维数由 @relative-artin-grothendieck-vanishing 得到。陈述 (1) 的其余部分，以及陈述 (2) 中普通的基变换，则把一般基变换用于 $S = Spec(k)$ 即可得到——这里 $S$ 只有一个点，它唯一的稠密开集就是自身。 

  // (3) 由截断，不妨设 $cal(K) = cal(F)$ 是可构造层。固定 $a$，并对下述命题 $T(r)$ 作归纳： 

  // - 对一切 $cal(L) in D^b_#[ctf] (S'_et, Lambda)$，只要 $cal(L) Lotimes_Lambda (-)$ 的上同调维数 $<=a$，#h(1fr)
  //   $
  //     h^q (g_Y^(-1) R f_* cal(F) Lotimes_Lambda cal(L)|_(Y')) -> h^q (R f'_* (g_X^(-1) cal(F) Lotimes_Lambda cal(L)|_(X')))
  //   $
  //   对一切 $q <= r$ 都是同构。 

  // 现在对任意满足下式的 $cal(L) in D^b_#[ctf] (S'_et, Lambda)$：$$
]

#corollary[
  (泛局部零调性) 设 $k$ 是任意域，$g: S -> Spec(k)$ 是任意有限型态射，$Lambda$ 是 $n$-挠 Noether 环且 $n in k^times$。则 $g$ 关于每个 $cal(K) in D^b_#[ctf] (S_et, Lambda)$ 都是泛局部零调的。 
]
#proof[
  由 @loc-acyc-and-base-change，以及 @rel-bc-reductions 证明中的第三步，以及第四步的前半部分，只需证明：对每个拉回图表： 
  #align(center, diagram({
    node((0, 0), [$X$])
    node((1, 0), [$Y$])
    node((0, 1), [$X_0$])
    node((1, 1), [$Y_0$])
    node((2, 1), [$Spec(k)$])
    node((2, 0), [$S$])
    edge((0, 1), (1, 1), [$f_0$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((1, 1), (2, 1), "->")
    edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
  }))
  其中 $X_0 -> Y_0$ 是有限型 $k$-概形之间的开浸入；则对每个可构造层 $cal(F) in cAb((X_0)_et, Lambda)$，记 $cal(K)_Y = cal(K)|_Y$，相对基变换： 
  $
    g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_Y -> R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_Y)
  $
  是同构。 

  为此我们想用类似 @cpct-generation-of-triangulated-cat 的生成论证。遗憾的是 $D^b_c$ 没有任意直和，故需放宽条件，允许 $cal(K) in D(S_et, Lambda)$ 是任意复形。现在由上一推论的 (2)，这里涉及的每个推前，都与底域从 $k$ 换成代数闭包 $ol(k)$ 这一步相容。于是基变换到 $ol(k)$，不妨设 $k$ 代数闭。现在： 
  
  - 在 $g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_Y -> R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_Y)$ 中，两边都是关于 $cal(K)$ 的三角函子； 

  - 对任意一族 $cal(K)_i in D(S_et, Lambda)$，有#h(1fr)
    $
      g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda (oplus.big_i cal(K)_(i,Y)) cong oplus.big_i (g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_(i,Y))
    $
    因为张量是左伴随，而： 
    $
      R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) (oplus.big_i cal(K)_(i,Y))) &cong R f_* (oplus.big_i g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_(i,Y)) \
      &cong oplus.big_i R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_(i,Y))
    $
    这里最后一步用到 @relative-limit-formula-for-sheaves 以及 $R f_*$ 的有界性。论证方法是先截断、再用极限公式，与 @derived-bounded-limit-formula-for-direct-sum 的证明大体相同。 

    因此，$g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_Y -> R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_Y)$ 的两边都与 $cal(K) in D(S_et, Lambda)$ 中的直和相容。 

  - 考虑 $D(S_et, Lambda)$ 中的对象族 ${j_! ul(Lambda)}$，其中 $j: U -> S$ 平展、$U$ 仿射。则： 

    - 若 $cal(K) in D(S_et, Lambda)$ 对一切平展、$U$ 仿射的 $j: U -> S$ 以及一切 $q in ZZ$ 都满足 $Hom_Lambda (j_! ul(Lambda)[q], cal(K)) = 0$，则把 $cal(K)$ 换成 K-内射消解 $cal(I)^bullet$ 后可见，对一切仿射 $U in Et_S$ 都有 $Gamma(U, h^q (cal(I))) = 0$。$Et_S$ 的每个对象都能被仿射对象覆盖，所以 $h^q (cal(I)) = 0$ 对一切 $q$ 成立，从而 $cal(K) = 0$。 

    - 每个 $j_! ul(Lambda)$ 都是紧对象。事实上，对平展、$U$ 仿射的 $j: U -> S$， 
      $
        Hom_Lambda (j_! ul(Lambda), oplus.big_i cal(K)_i) &cong h^0 (R Gamma(U, oplus.big_i cal(K)_i)) \
        &cong h^0 (oplus.big_i R Gamma(U, cal(K)_i)) \
        &cong oplus.big_i h^0 (R Gamma(U, cal(K)_i))
      $
      其中第二步用到 @derived-bounded-limit-formula-for-direct-sum。这里 $S$ 是代数闭域 $k$ 上的有限型概形，$U$ 也是，于是 $R Gamma(U, -)$ 的上同调维数有上界。 

  因此，援引 @cpct-generation-of-triangulated-cat，只需对一切仿射平展的 $j: U -> S$ 证明： 
  $
    g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda cal(K)_Y -> R f_* (g_X^(-1) cal(F) Lotimes_Lambda f^(-1) cal(K)_Y)
  $
  当 $cal(K) = j_! ul(Lambda)$ 时它是同构。现在由 Zariski 主定理，可取紧化 $j: U ->^ell ol(U) ->^pi S$，其中 $pi$ 有限。取 $ell$ 的补闭浸入 $i: Z -> ol(U)$，并置 $pi' = pi compose i$。由零延拓三角与 @etale-and-compactified-lower-shriek-agree，得到正合列： 
  $
    0 -> j_! ul(Lambda) -> pi_* ul(Lambda) -> pi'_* ul(Lambda) -> 0
  $
  因此只需对一切有限态射 $pi: S' -> S$ 且 $cal(K) = pi_* ul(Lambda)$ 的情形证明。作拉回图表： 
  #align(center, diagram({
    node((0, 0), [$X$])
    node((1, 0), [$Y$])
    node((0, 1), [$X_0$])
    node((1, 1), [$Y_0$])
    node((0, -1), [$X'$])
    node((1, -1), [$Y'$])
    node((2, -1), [$S'$])
    node((2, 1), [$Spec(k)$])
    node((2, 0), [$S$])
    edge((0, 1), (1, 1), [$f_0$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((1, 1), (2, 1), "->")
    edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
    edge((0, -1), (1, -1), $f'$, "->")
    edge((1, -1), (2, -1), "->")
    edge((2, -1), (2, 0), $pi$, label-side: left, "->")
    edge((1, -1), (1, 0), $pi_Y$, label-side: left, "->")
    edge((0, -1), (0, 0), $pi_X$, "->")
  }))
  注意 $cal(K)_Y cong pi_(Y,*) ul(Lambda), f^(-1) cal(K)_Y cong pi_(X,*) ul(Lambda)$。计算： 
  $
    g_Y^(-1) R f_(0,*) cal(F) Lotimes_Lambda pi_(Y,*) ul(Lambda) &cong pi_(Y,*) pi_Y^(-1) g_Y^(-1) R f_(0,*) cal(F) #[由投影公式] \
    &cong pi_(Y,*) R f'_* pi_X^(-1) g_X^(-1) cal(F) #[由上一推论 (2) 中的一般基变换] \
    &cong R f_* pi_(X,*) pi_X^(-1) g_X^(-1) cal(F) \
    &cong R f_* (g_X^(-1) cal(F) Lotimes_Lambda pi_(X,*) ul(Lambda)) #[由投影公式]
  $
  至此完成。 
]

我们还要为 $R f^!$ 建立某种一般基变换。 

#proposition[
  设 $S$ 是 Noether 的 $ZZ[n^(-1)]$-概形，$Lambda$ 是 $n$-挠 Noether 环，$f: X -> Y$ 是有限型 $S$-概形之间的分离态射，$cal(K) in D^b_c (Y_et, Lambda)$。则存在 $S$ 的稠密开集 $U$，使得对任意拉回图表： 
  #align(center, diagram({
    node((0, 0), [$X'$])
    node((1, 0), [$Y'$])
    node((0, 1), [$X$])
    node((1, 1), [$Y$])
    // node((0.3, 0.3), [$cart$])
    node((2, 1), [$S$])
    node((2, 0), [$S'$])
    edge((0, 1), (1, 1), [$f$], label-side: right, "->")
    edge((0, 0), (1, 0), [$f'$], label-side: left, "->")
    edge((1, 0), (2, 0), "->")
    edge((1, 1), (2, 1), "->")
    edge((1, 0), (1, 1), [$g_Y$], label-side: left, "->")
    edge((2, 0), (2, 1), [$g$], label-side: left, "->")
    edge((0, 0), (0, 1), [$g_X$], label-side: right, "->")
  }))
  其中 $g(S') subset U$，基变换映射
  $
    g_X^(-1) R f^! cal(K) -> R f'^! g_Y^(-1) cal(K)
  $
  （由沿紧合基变换同构 $R f'_! g_X^(-1) cong g_Y^(-1) R f_!$ 的转置 Beck–Chevalley 基变换诱导）是同构。 
]
#proof[
  由 @bcbc-horizontal-concat 与 @bcbc-vertical-concat 容易验证，$R f^!$ 的这个基变换映射与拉回方块的水平、竖直拼接相容。 

  在本证明中，若开集 $U subset S$ 使本命题的陈述成立，我们就称它为 $S$ 的 $(f, cal(K), S)$-好开集。 

  这个问题在 $Y$ 上是 Zariski 局部的。取仿射覆盖 ${j_(Y,i): Y_i -> Y}$，把 $f$ 基变换为 $f_i: X_i -> Y_i$。若 $U$ 对一切 $i$ 都是 $(f_i, cal(K)|_(Y_i), S)$-好的，则： 
  $
    g_(X_i)^(-1) R f_i^! (cal(K)|_(Y_i)) cong R f'_i^! g_(Y_i)^(-1) (cal(K)|_(Y_i))
  $
  这就是说 $(g_X^(-1) R f^! cal(K))|_(X'_i) cong (R f'^! g_Y^(-1) cal(K))|_(X'_i)$。于是由 @surjective-pullback-conservative，$g_X^(-1) R f^! cal(K) cong R f'^! g_Y^(-1) cal(K)$。 

  因此不妨设 $Y$ 仿射。再取 $X$ 的仿射覆盖 ${j_i: X_i -> Y}$。若 $U$ 对一切 $i$ 都是 $(f compose j_i, cal(K), S)$-好的，这就是说：对满足 $g(S') subset U$ 的 $g: S' -> S$， 
  $
    j'_i^(-1) g_X^(-1) R f^! cal(K) cong g_(X_i)^(-1) j_i^(-1) R f^! cal(K) cong j'_i^(-1) R f'^! g_Y^(-1) cal(K)
  $
  对一切 $i$ 成立。于是由 @surjective-pullback-conservative，$g_X^(-1) R f^! cal(K) cong R f'^! g_Y^(-1) cal(K)$，从而 $U$ 是 $(f, cal(K), S)$-好的。这样便可以在 $X$ 上作 Zariski 局部论证，设 $X$ 仿射且其像落在 $Y$ 的某个仿射开集之中。于是 $X$ 也是仿射的。于是可把 $f$ 分解为 $X ->^i AA^m_Y ->^p Y$，其中 $i$ 是闭浸入。现在： 
  $
    g_X^(-1) R f^! cal(K) cong g_X^(-1) R i^! p^(-1) cal(K)(m)[2m] \
    R f'^! g_Y^(-1) cal(K) cong R i'^! p'^(-1) g_Y^(-1) cal(K)(m)[2m] cong R i'^! g_(AA^m_Y)^(-1) p^(-1) cal(K)(m)[2m]
  $
  这里用到相对 Poincaré 对偶。因此把 $f$ 换成 $i$、把 $cal(K)$ 换成 $p^(-1) cal(K)(m)[2m]$，便可设 $f=i$ 是闭浸入。现在取补开浸入 $j: U -> Y$，用带支集截面三角： 
  $
    R i^! cal(K) -> i^(-1) cal(K) -> i^(-1) R j_* j^(-1) cal(K) ->^(+1)
  $
  由一般基变换，可缩小 $S$，使 $R j_* j^(-1) cal(K)$ 的构造与任意基变换交换。现在三角的第二、第三项都与基变换相容，第一项也是。至此完成。 
]

最后，作为应用，我们证明 $D^b_#[ctf]$ 对平展层上已定义的六种基本构造封闭；这六种构造合称_Grothendieck 六函子_。 

#theorem(name: <finiteness-of-six-functors>)[
  (六函子的有限性) 设 $k$ 是域，$f: X -> Y$ 是分离 $k$-概形之间的态射，$Lambda$ 是 $n$-挠 Noether 环且 $n in k^times$。则下列函子： 
  $
    R f_*, R f_! : D(X_et, Lambda) -> D(Y_et, Lambda) \
    f^(-1), R f^!: D(Y_et, Lambda) -> D(X_et, Lambda) \
    - Lotimes_Lambda -: D(X_et, Lambda) times D(X_et, Lambda) -> D(X_et, Lambda) \
    RHHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(X_et, Lambda)
  $
  都把 $D^b_#[ctf]$ 送到 $D^b_#[ctf]$，其中前四个上有界且下有界。 
]
#proof[
  其中三条已经知道： 

  - 由 @constructible-sheaves-first-props (1)，$f^(-1)$ 保持 $D^b_c$；逐茎检查可知它保持有限 Tor 幅度； 

  - 由 @finiteness-of-lower-shriek，$R f_!$ 保持 $D^b_c$；由 Grothendieck 消没，它有界。由投影公式，它保持 $D^b_#[ctf]$：#h(1fr)
    $
      R f_! cal(K) Lotimes_Lambda cal(L) cong R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))
    $
    事实上，设 $cal(K)$ 的 Tor 幅度在 $[a,b]$ 中，$cal(L)$ 集中在 $[a',b']$ 中。则 $cal(K) Lotimes_Lambda f^(-1) cal(L)$ 集中在 $[a+a', b+b']$，故 $R f_! (cal(K) Lotimes_Lambda f^(-1) cal(L))$ 集中在 $[a+a', b+b'+2d]$，其中 $d$ 是 $f$ 的最大纤维维数。因此 $R f_! cal(K)$ 的 Tor 幅度在 $[a, b+2d]$ 中。 

  - $- Lotimes_Lambda -$ 保持 $D^b_#[ctf]$。事实上，对 $cal(K)_(1,2) in D^b_#[ctf] (X_et, Lambda)$，由 @resolution-of-ctf-complexes 可取它们的有界平坦消解 $cal(P)_(1,2)^bullet$，其中每一项 $cal(P)^q_(1,2)$ 都可构造且平坦。此时 $Lotimes$ 可以逐项计算： 
    $
      cal(K)_1 Lotimes_Lambda cal(K)_2 cong cal(P)^bullet_1 otimes_Lambda cal(P)^bullet_2
    $
    现在可构造层的张量仍可构造（在分层上检查即可），平坦层的张量仍平坦（形式地）。因此复形 $cal(P)^bullet_1 otimes_Lambda cal(P)^bullet_2$ 的每一项都是可构造且平坦的层——它是若干可构造平坦层张量的有限直和。故 $cal(K)_1 Lotimes_Lambda cal(K)_2 in D^b_#[ctf] (X_et, Lambda)$。 

  下一个要处理的函子是 $R f_*$。 

  - 由 @finiteness-of-rf-lower-star，$R f_*$ 保持 $D^b_c$ 且上有界。故只需证明它保持有限 Tor 幅度。#h(1fr)

    为此我们断言：对任意复形 $M in D(Lambda)$，投影映射给出同构
    $
      R f_* cal(K) Lotimes_Lambda ul(M)_Y cong R f_* (cal(K) Lotimes_Lambda ul(M)_X)
    $
    事实上，这个关于 $M$ 的性质在平移与补全特殊三角下不变，因为两边都是关于 $M$ 的三角函子。进一步，两边都与 $M$ 中的任意直和交换：这由与 @derived-bounded-limit-formula-for-direct-sum 中相同的截断论证得到，只不过这次用的是 $R f_*$ 的有界性而非 $R Gamma$。最后，当 $M = Lambda$ 时两边都是 $R f_* cal(K)$，投影是同构。于是由 @cpct-generator-of-d-lambda，断言得证。 

    特别地，设 $d$ 是 $R f_*$ 的上同调维数上界，$[a,b]$ 是 $cal(K)$ 的 Tor 幅度。则我们已证明：对 $Y$ 的每个几何点 $ol(y)$ 与每个支撑在 $[a',b']$ 上的 $Lambda$-模复形 $M$，
    $
      h^q ((R f_* cal(K))_(ol(y)) Lotimes_Lambda M) = 0, forall q in.not [a+a',b+b'+d]
    $
    于是逐茎检查可知：对每个支撑在 $[a',b']$ 上的复形 $cal(L) in D(Y_et, Lambda)$，当 $q in.not [a+a',b+b'+d]$ 时 $h^q (R f_* cal(K) Lotimes_Lambda cal(L)) = 0$。故 $R f_* cal(K)$ 的 Tor 幅度在 $[a,b+d]$ 中。 

  接下来，$R f^!$ 的情形可由 $R f_!$ 形式地推出。 

  - 对闭浸入 $i: Z -> X$ 及其补开浸入 $j: U -> X$，有带支集截面三角： 
    $
      i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
    $
    现在： 
    
    - 由于 $R j_*$ 有界，$i_* R i^!$ 也有界。作用 $i^(-1)$ 便知 $R i^!$ 有界； 

    - 如上论证，$R j_* j^(-1)$ 保持 $D^b_#[ctf]$，故 $i_* R i^!$ 也保持。作用 $i^(-1)$ 便知 $R i^!$ 保持 $D^b_#[ctf]$。 

  - 对一般的有限型分离态射 $f: X -> Y$，用有限多个仿射开集 ${X_i}$ 覆盖 $X$，使每个都落在 $Y$ 的某个仿射开集之上。取 $X' = union.big_i X_i$ 与局部同构 $j: X' -> X$。则 $f compose j$ 可分解为 $X ->^i AA^d_Y ->^p Y$，其中 $i$ 是闭浸入。于是 
    $
      j^(-1) R f^! cal(K) cong R i^! R p^! cal(K)
    $
    由相对 Poincaré 对偶，$R p^! cal(K) cong cal(K)(d)[2d]$。故 $j^(-1) R f^! cal(K) cong R i^! R p^! cal(K) cong R i^! cal(K) (d)[2d]$。既然 $R i^!$ 有界且保持 $D^b_#[ctf]$，$j^(-1) R f^! cal(K)$ 也具有这两条性质。 

    现在可构造性可以局部检查，故 $R f^!$ 保持 $D^b_c$。逐茎检查可知 $R f^!$ 保持 $D^b_#[ctf]$。 

  最后一个要检查的函子是 $RHHom_Lambda (-, -)$。 

  - 要证 $RHHom_Lambda (-, -)$ 保持 $D^b_#[ctf]$，由截断与 @resolution-of-ctf-complexes，只需证明：对任意平坦可构造层 $cal(F), cal(G) in cAb(X_et, Lambda)$，都有 $RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf] (X_et, Lambda)$。 
    
    令： 
    $
      cal(S)_X = {Z subset X #[closed]:& RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf] #[对任意平坦可构造层 $cal(F), cal(G) in cAb(X_et, Lambda) $ \
      $&$只要 $supp(cal(F)) subset Z$]}
    $

    我们打算对 $cal(S)_X$ 作 Noether 归纳。注意： 

    - 设 $i: Z -> X$ 是闭子概形。对任意满足 $supp(cal(F)) subset Z$ 的平坦可构造层 $cal(F), cal(G) in cAb(X_et, Lambda)$，则 $cal(F)$ 可写成 $cal(F) = i_* cal(F)_Z$，其中 $cal(F)_Z$ 是 $Z$ 上的平坦可构造层。现在： 
      $
        RHHom_Lambda (i_* cal(F)_Z, cal(G)) cong i_* RHHom_Lambda (cal(F)_Z, R i^! cal(G))
      $
      如前所述 $R i^! cal(G) in D^b_#[ctf] (Z_et, Lambda)$，故设 $Z in cal(S)_Z$，则由截断可知 $RHHom_Lambda (cal(F)_Z, R i^! cal(G)) in D^b_#[ctf] (Z_et, Lambda)$。作用 $i_*$ 保持 $D^b_#[ctf]$，这就证明了 $Z in cal(S)_X$。 

      另一方面，对可构造平坦层 $cal(F)_Z, cal(G)_Z in cAb(Z_et, Lambda)$， 
      $
        RHHom_Lambda (cal(F)_Z, cal(G)_Z) cong i^(-1) RHHom(i_* cal(F)_Z, i_* cal(G)_Z)
      $
      因此 $Z in cal(S)_X$ 蕴含 $Z in cal(S)_Z$。 
    
    于是 $Z in cal(S)_X$ 当且仅当 $Z in cal(S)_Z$。这样，为作 Noether 归纳，只需验证： 

    - 若每个真闭子集 $Z subset.neq X$ 都属于 $cal(S)_X$，则 $X in cal(S)_X$。 

    下面开始验证这一点。对任意平坦可构造层 $cal(F), cal(G) in cAb(X_et, Lambda)$，取非空开集 $U subset X$ 使 $cal(F)|_U$ 常值。取互补的浸入 $j: U -> X$ 与 $i: Z = X - U -> X$，便有零延拓三角： 
    $
      j_! j^(-1) cal(F) -> cal(F) -> i_* i^(-1) cal(F) ->^(+1)
    $ 
    现在 $supp(i_* i^(-1) cal(F)) subset Z in cal(S)_X$，故 $RHHom_Lambda (i_* i^(-1) cal(F), cal(G)) in D^b_#[ctf]$。于是只需再证 $RHHom_Lambda (j_! j^(-1) cal(F), cal(G)) in D^b_#[ctf]$。事实上， 
    $
      RHHom_Lambda (j_! j^(-1) cal(F), cal(G)) cong R j_* RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G))
    $
    现在 $R j_*$ 保持 $D^b_#[ctf]$，故只需证明 $RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G)) in D^b_#[ctf]$。而 $j^(-1) cal(F)$ 局部常值，于是把 $X$ 换成 $U$ 后，只需证明： 

    - 若 $cal(F), cal(G) in cAb(X_et, Lambda)$ 可构造且平坦，且 $cal(F)$ 是 l.c.c.，则 $RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf]$。 

    取平展覆盖 $j: U -> X$，其中 $U$ 仿射，使 $j^(-1) cal(F)$ 常值。假定我们能证明 $j^(-1) RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf]$。那么： 

    - $j^(-1) EExt^q_Lambda (cal(F), cal(G))$ 可构造，且除有限多个 $q$ 之外消没。 

      由于 $j$ 满射，由 @surjective-pullback-conservative，$EExt^q_Lambda (cal(F), cal(G))$ 在有限多个 $q$ 之外消没。进一步，对一切 $cal(H)$，$cal(H) -> j_! j^(-1) cal(H)$ 都是单射，故所有 $EExt^q_Lambda (cal(F), cal(G))$ 都可构造。 

      因此 $RHHom_Lambda (cal(F), cal(G)) in D^b_c$。 

    - 逐茎检查即可提升为 $RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf]$。 

    现在 $j^(-1) RHHom_Lambda (cal(F), cal(G)) in D^b_#[ctf] cong RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G))$，故把 $X$ 换成 $U$，并注意 $j^(-1) cal(F)$ 常值，就只剩下证明： 

    - 若 $cal(G) in cAb(X_et, Lambda)$ 可构造且平坦，$M$ 是有限平坦 $Lambda$-模，则 $RHHom_Lambda (ul(M), cal(G)) in D^b_#[ctf]$。 

    Noether 环上的有限平坦模必定投射，且局部自由。故 $M$ 是投射的局部自由 $Lambda$-模。 
    
    #lemma[
      设 $Lambda$ 是 Noether 环，$M$ 是有限 $Lambda$-模，$N$ 是任意 $Lambda$-模。则对任意概形 $X$， 
      $
        EExt^q_Lambda (ul(M)_X, ul(N)_X) = ul(Ext^q_Lambda (M, N))
      $
    ]
    #proof[
      先对 $N$ 内射的情形证明。也就是说，要证对一切 $q >= 1$ 都有 $EExt^q_Lambda (ul(M)_X, ul(N)_X) = 0$。取一个由有限自由 $Lambda$-模组成的消解 $dots.c -> P^(-1) -> P^0 -> M -> 0$。则 $HHom_Lambda (ul(P^(-p)), -)$ 正合，于是 $EExt^q_Lambda (ul(M)_X, -)$ 可计算为： 
      $
        EExt^q_Lambda (ul(M)_X, -) &cong h^q (0 -> HHom_Lambda (ul(P^0)_X, ul(N)_X) -> HHom_Lambda (ul(P^(-1))_X, ul(N)_X) -> dots.c) \
        &cong h^q (0 -> ul(Hom_Lambda (P^0, N))_X -> ul(Hom_Lambda (P^(-1), N))_X -> dots.c) \
        &cong ul(h^q (0 -> Hom_Lambda (P^0, N) -> Hom_Lambda (P^(-1), N) -> dots.c))_X \
        &= 0
      $ 
      其中最后的消没是因为 $N$ 是内射 $Lambda$-模。现在看一般情形，取 $N$ 的内射消解 $0 -> N -> I^0 -> I^1 -> dots.c$。由于对一切 $p>=1$，$EExt^p_Lambda (ul(M)_X, ul(I^q)_X)$ 都消没，这个消解可用来计算 $EExt^p_Lambda (ul(M)_X, ul(N)_X)$： 
      $
        EExt^p_Lambda (ul(M)_X, ul(N)_X) &cong h^p (0 -> HHom_Lambda (ul(M)_X, ul(I^0)_X) -> HHom_Lambda (ul(M)_X, ul(I^1)_X) -> dots.c) \
        &cong ul(h^p (0 -> Hom_Lambda (M, I^0) -> Hom_Lambda (M, I^1) -> dots.c))_X \
        &cong ul(Ext^p_Lambda (M, N))
      $
      至此完成。 
    ]

    由 @finite-morphisms-and-constructible-sheaves，可取 $cal(G)$ 的一个消解： 
    $
      0 -> cal(G) -> r_(0,*) ul(N^0) -> r_(1,*) ul(N^1) -> dots.c
    $
    其中 $N^q$ 是有限 $Lambda$-模，$r_q: X_q -> X$ 有限。现在： 
    $
      EExt^q_Lambda (ul(M), r_(p,*) ul(N^p)) = r_(p,*) EExt^q_Lambda (ul(M)_(X_q), ul(N^p)_(X_q)) 
    $
    由上一条引理，当 $q>=1$ 时它消没，因为 $M$ 是投射 $Lambda$-模。因此上面 $cal(G)$ 的消解适合用来计算 $EExt^q_Lambda (ul(M), cal(G))$，并且： 

    $
      EExt^q_Lambda (ul(M), cal(G)) cong h^q (dots.c -> HHom_Lambda (ul(M), r_(q-1,*) ul(N^(q-1))) -> HHom_Lambda (ul(M), r_(q,*) ul(N^q)) -> HHom_Lambda (ul(M), r_(q+1,*) ul(N^(q+1))) -> dots.c)
    $
    // 按我们对消解的选取，可以做到使每个 $r^q: X_q -> X$ 分解为 $X_q ->^(g^q) X_(q-1) ->^(r^(q-1)) X$。于是， 
    // $
    //   EExt^q_Lambda (ul(M), cal(G)) cong r^(q-1)_* h^q (ul(Hom_Lambda (M, N^(q-1))) -> g^(q-1)_* ul(Hom_Lambda (M, N^q)) -> g^(q-1)_* g^q_*)
    // $
    取茎之后，它就是下面复形的上同调： 
    $
      dots.c -> Hom_Lambda (M, oplus.big_(ol(x_(q-1)) in r_(q-1)^(-1) (ol(x))) N^(q-1)) -> Hom_Lambda (M, oplus.big_(ol(x_(q)) in r_(q)^(-1) (ol(x))) N^(q)) -> Hom_Lambda (M, oplus.big_(ol(x_(q+1)) in r_(q+1)^(-1) (ol(x))) N^(q+1)) -> dots.c
    $
    当 $q >= 1$ 时，$oplus.big_(ol(x_(q-1)) in r_(q-1)^(-1) (ol(x))) N^(q-1) -> oplus.big_(ol(x_(q)) in r_(q)^(-1) (ol(x))) N^(q) -> oplus.big_(ol(x_(q+1)) in r_(q+1)^(-1) (ol(x))) N^(q+1)$ 正合，因为它是 $cal(G)$ 的消解取茎所得。又 $M$ 投射，故上面的复形在 $q$ 处正合。这就证明了： 
    $
      RHHom_Lambda (ul(M), cal(G)) = HHom_Lambda (ul(M), cal(G)) = ker(r_(0,*) Hom_Lambda (M, N^0) -> r_(1,*) Hom_Lambda (M, N^1))
    $
    它是可构造的。如上取茎检查，便知： 
    $
      HHom_Lambda (ul(M), cal(G))_(ol(x)) cong Hom_Lambda (M, cal(G)_(ol(x)))
    $
    由于 $M$ 局部自由，$M$ 可对偶化，其对偶 $caron(M)$ 也局部自由。故 $Hom_Lambda (M, cal(G)_(ol(x))) cong caron(M) otimes_Lambda cal(G)_(ol(x))$ 平坦。 

    总之，$RHHom_Lambda (ul(M), cal(G)) = Hom_Lambda (ul(M), cal(G))$ 可构造且平坦，证毕。 
]
