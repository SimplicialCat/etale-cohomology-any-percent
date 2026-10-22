#import "void-import.typ": *
== Verdier 对偶

本节我们建立所谓的 Verdier 对偶：一个关于平展层复形可对偶性的结果。这也是平展上同调理论中的最后一块拼图。 

本节的做法与 @cite-lei-fu[Section 9.6] 十分接近，只是把讨论限制在底为域的情形。@cite-lei-fu 中的有限性与双对偶论证在正则的 $1$ 维底上同样成立；想要更一般的结果，就该去那里看看。 

#definition(name: <defn-dualizing-complex-functor>)[
  设 $f: X -> Spec(k)$ 是有限型的分离态射，其中 $k$ 是域，$Lambda$ 是 $n$-挠 Noether 环，且 $n in k^times$。则定义*对偶复形* (dualizing complex) 函子为如下反变函子： 
  $
    DD_X = DD_(X\/k): D^b_#[ctf] (X_et, Lambda)^opp &-> D^b_#[ctf] (X_et, Lambda) \
    
    cal(K) &|-> RHHom_Lambda (cal(K), R f^! Lambda)
  $
  这里之所以能保持在 $D^b_#[ctf]$ 中，靠的是 @finiteness-of-six-functors，即六函子的有限性。 

  现在按定义，存在一个 $Lambda$-双线性求值配对： 
  $
    cal(K) Lotimes_Lambda RHHom_Lambda (cal(K), R f^! Lambda) -> R f^! Lambda
  $
  这由伴随性诱导出自然映射 $cal(K) -> DD_X DD_X cal(K)$。 
]

双对偶的陈述是：自然映射 $cal(K) -> DD_X DD_X cal(K)$ 恒为同构。 

#lemma[
  双对偶映射 $cal(K) -> DD_X DD_X cal(K)$ 对一切 $cal(K) in D^b_#[ctf] (X_et, Lambda)$ 都是同构，前提是 $X = Spec(k)$ 本身，且 $k$ 可分闭。 
]
#proof[
  要证的是：对任意复形 $M^bullet$，它由有限平坦 $Lambda$-模构成，
  $
    M^bullet -> RHom_Lambda (RHom_Lambda (M^bullet, Lambda), Lambda)
  $
  是同构。事实上，每个 $M^q$ 在 Noether 环 $Lambda$ 上有限平坦，从而是投射的、局部自由的。因此映射 $M^bullet -> RHom_Lambda (RHom_Lambda (M^bullet, Lambda), Lambda)$ 逐项由下式给出： 
  $
    M^q -> Hom_Lambda (Hom_Lambda (M^q, Lambda), Lambda)
  $
  由于 $M^q$ 有限局部自由，该映射是同构。 
]

#lemma(name: <partial-biduality-in-proper-case>)[
  若 $f: X -> Spec(k)$ 紧合、$k$ 可分闭，则对一切 $cal(K) in D^b_#[ctf] (X_et, Lambda)$，双对偶映射 $cal(K) -> DD_X DD_X cal(K)$ 在两边作用 $R Gamma(X, -)$ 之后是同构。 
]
#proof[
  由于 $f$ 紧合，$R f_* = R f_!$。由 @existence-of-upper-shriek (4)，存在自然同构： 
  $
    RHHom_Lambda (R f_* cal(K), Lambda) cong R f^! RHHom_Lambda (cal(K), R f^! Lambda)
  $
  换言之，$DD_(Spec(k)) R f_* cal(K) cong R f_* DD_X cal(K)$。于是有同构： 
  $
    R f_* DD_X DD_X cal(K) cong DD_(Spec(k)) DD_(Spec(k)) R f_* cal(K) cong R f_* cal(K)
  $
  我们断言该同构由求值诱导。也就是说，需要验证下图交换： 
  // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwwLCJSSEhvbV9MYW1iZGEgKFJISG9tX0xhbWJkYSAoUiBmXyogY2FsKEspLCBMYW1iZGEpLCBMYW1iZGEpIl0sWzAsMSwiUkhIb21fTGFtYmRhIChSIGZfKiBSSEhvbV9MYW1iZGEgKGNhbChLKSwgUiBmXiEgTGFtYmRhKSwgTGFtYmRhKSJdLFswLDIsIlIgZl8qIFJISG9tX0xhbWJkYSAoUkhIb21fTGFtYmRhIChjYWwoSyksIFIgZl4hIExhbWJkYSksIFIgZl4hIExhbWJkYSkiXSxbMiwwLCJSIGZfKiBjYWwoSykiXSxbMiwyLCJSIGZfKiBjYWwoSykiXSxbMyw0LCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzAsMSwidGlsZGUiLDJdLFsyLDEsInRpbGRlIl0sWzMsMCwiZXYiLDJdLFs0LDIsImV2Il1d
  #align(center, diagram({
    node((0, 0), [$RHHom_Lambda (RHHom_Lambda (R f_* cal(K), Lambda), Lambda)$])
    node((0, 1), [$RHHom_Lambda (R f_* RHHom_Lambda (cal(K), R f^! Lambda), Lambda)$])
    node((0, 2), [$R f_* RHHom_Lambda (RHHom_Lambda (cal(K), R f^! Lambda), R f^! Lambda)$])
    node((2, 0), [$R f_* cal(K)$])
    node((2, 2), [$R f_* cal(K)$])
    edge((2, 0), (2, 2), "=")
    edge((0, 0), (0, 1), [$tilde$], label-side: right, "->")
    edge((0, 2), (0, 1), [$tilde$], label-side: left, "->")
    edge((2, 0), (0, 0), [$"ev"$], label-side: right, "->")
    edge((2, 2), (0, 2), [$"ev"$], label-side: left, "->")
  }))
  去柯里化之后，上方的路径变成映射： 
  $
    R f_* cal(K) Lotimes_Lambda R f_* RHHom_Lambda (cal(K), R f^! Lambda) cong R f_* cal(K) Lotimes_Lambda RHHom_Lambda (R f_* cal(K), Lambda) ->^"ev" Lambda
  $
  而下方路径变成： 
  $
    R f_* cal(K) Lotimes_Lambda R f_* RHHom_Lambda (cal(K), R f^! Lambda) -> R f_* (cal(K) Lotimes_Lambda RHHom_Lambda (cal(K), R f^! Lambda)) ->^"ev" R f_* R f^! Lambda ->^Tr Lambda
  $
  这两条路径形式地相等。于是我们证明了求值 $R f_* cal(K) -> R f_* DD_X DD_X cal(K)$ 是同构。$k$ 是可分闭域，故这等价于说 $R Gamma(X, cal(K)) -> R Gamma(X, DD_X DD_X cal(K))$ 是同构。 
]

/*
要继续推进，我们本来需要一个极限公式，才能从任意域基变换到可分闭域。换个办法，我们来做一次 _devissage_。 

#lemma(name: <base-field-extension-for-upper-shriek>)[
  设 $L\/k$ 是任意域扩张，$f: X -> Y$ 是有限型 $k$-概形之间的分离态射，$f_L: X_L -> Y_L$ 是它从 $k$ 到 $L$ 的基变换。则对任意 $cal(K) in D^b_#[ctf] (Y_et, Lambda)$，存在典范的自然同构： 
  $
    (R f^! cal(K))|_(X_L) cong R f_L^! (cal(K)|_(Y_L))
  $
]
#proof[
  先设 $f = i$ 是闭浸入，并取补的开浸入 $j: U -> Y$。于是有带支集截面的三角： 
  $
    i_* R i^! cal(L) -> cal(L) -> R j_* j^(-1) cal(L) ->^(+1)
  $
  以及： 
  $
    i_(L,*) R i_L^! cal(L)|_(Y_L) -> cal(L)|_(Y_L) -> R j_(L,*) j_L^(-1) cal(L)|_(Y_L) ->^(+1)
  $
  然而由一般基变换，$(R j_* j^(-1) cal(L))|_(Y_L) cong R j_(L,*) j_L^(-1) cal(L)|_(Y_L)$。于是在该特殊三角的第一项上有： 
  $
    i_(L,*) (R i^! cal(L))|_(X_L) cong (i_* R i^! cal(L))|_(Y_L) cong i_(L,*) R i_L^! cal(L)|_(Y_L)
  $
  从而 $(R i^! cal(L))|_(X_L) cong R i_L^! cal(L)|_(Y_L)$。 

  其次设 $f = p: AA^d_Y -> Y$。则由相对 Poincaré 对偶，两边都是 $cal(K)|_(X_L)(d)[2d]$，因而同构。 

  现在处理一般情形。取 $X$ 的一个仿射覆盖，便有平展覆盖 $j: U -> X$，使 $f compose j$ 分解为 $U ->^i AA^d_k ->^p Spec(k)$，其中 $i$ 是闭浸入。于是由前两种情形，该引理对 $f compose j$ 成立。因此： 
  $
    j_L^(-1) (R f^! cal(K))|_(X_L) cong j_L^(-1) R f_L^! cal(K)|_(Y_L)
  $
  由于 $j$ 是满射，由 @surjective-pullback-conservative 便得到 $R f^! cal(K))|_(X_L) cong R f_L^! cal(K)|_(Y_L)$。 
]

#lemma[
  设 $L\/k$ 是任意域扩张，$X$ 是有限型 $k$-概形。令 $X_L = X otimes_k k_L$。则对任意 $cal(K), cal(L) in D^b_#[ctf] (X_et, Lambda)$， 
  $
    RHHom_Lambda (cal(K), cal(L))|_(X_L) -> RHHom_Lambda (cal(K)|_(X_L), cal(L)|_(X_L))
  $
  是同构。 
]
#proof[
  对 $d = dim(X)$ 归纳，不妨设本引理对所有 $X$ 都已证，只要 $dim(X) <= d-1$。 

  由 @resolution-of-ctf-complexes 与截断，只需对 $cal(F), cal(G)$ 证明即可，其中二者都是 $X$ 上 $Lambda$-模的可构造平坦层： 
  $
    RHHom_Lambda (cal(F), cal(G))|_(X_L) cong RHHom_Lambda (cal(F)|_(X_L), cal(G)|_(X_L))
  $
  由于 $cal(F)$ 可构造，存在稠密开集 $U subset X$，使 $cal(F)$ 在其上局部常值。适当缩小 $U$，不妨设 $cal(F), cal(G)$ 在 $U$ 上都是 l.c.c.。现在取互补的浸入 $j: U -> X, i: Z -> X$ 与 $j_L: U_L -> X_L, i_L: Z_L -> X_L$。则： 
  $
    RHHom_Lambda (i_* i^(-1) cal(F), cal(G))|_(X_L) &cong i_(L,*) (RHHom_Lambda (i^(-1) cal(F), R i^! cal(G))|_(Z_L)) \
    &cong i_(L,*) RHHom_Lambda (i_L^(-1) cal(F)|_(X_L), (R i^! cal(G))|_(Z_L)) #[由归纳假设] \
    &cong i_(L,*) RHHom_Lambda (i_L^(-1) cal(F)|_(X_L), R i_L^! (cal(G)|_(X_L))) #[由前一引理]\
    &cong RHHom_Lambda (i_(L,*) i_L^(-1) cal(F)|_(X_L), cal(G)|_(X_L))
  $
  于是由零延拓三角，只需证明： 
  $
    RHHom_Lambda (j_! j^(-1) cal(F), cal(G))|_(X_L) cong RHHom_Lambda (j_(L,!) j_L^(-1) cal(F)|_(X_L), cal(G)|_(X_L))
  $
  事实上，
  $
    RHHom_Lambda (j_! j^(-1) cal(F), cal(G))|_(X_L) cong (R j_* RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G)))|_(X_L) cong R j_(L,*) (RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G))|_(U_L))
  $
  可由一般基变换得到；而： 
  $
    RHHom_Lambda (j_(L,!) j_L^(-1) cal(F)|_(X_L), cal(G)|_(X_L)) cong R j_(L,*) RHHom_Lambda (j_L^(-1) cal(F)|_(X_L), j_L^(-1) cal(G)|_(X_L))
  $
  于是只需证明： 
  $
    RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G))|_(U_L) cong RHHom_Lambda (j_L^(-1) cal(F)|_(X_L), j_L^(-1) cal(G)|_(X_L))
  $
  换言之，把 $X$ 换作 $U$，只需证明： 
  
  - 对任意 l.c.c. 平坦 $Lambda$-模层 $cal(F), cal(G)$，它们都定义在 $X$ 上，#h(1fr)
    $
      RHHom_Lambda (cal(F), cal(G))|_(X_L) cong RHHom_Lambda (cal(F)|_(X_L), cal(G)|_(X_L))
    $

  存在平展覆盖 $j: U -> X$，其中 $U$ 仿射，且 $j^(-1) cal(F), j^(-1) cal(G)$ 都是常值的。沿 @surjective-pullback-conservative 拉回后验证即可。于是实际上不妨设 $cal(F), cal(G)$ 是常值层 $ul(F), ul(G)$，其中 $Lambda$-模 $F,G$ 都是有限投射的。这时我们已经看到： 
  $
    RHHom_Lambda (cal(F), cal(G))|_(X_L) cong ul(Hom_Lambda (F, G)) cong RHHom_Lambda (cal(F)|_(X_L), cal(G)|_(X_L))
  $
  至此完成。 
]

#corollary(name: <dualizing-complex-and-base-field-ext>)[
  设 $k$ 是任意域，$X$ 是有限型分离的 $k$-概形。令 $X_L = X otimes_k k_L$。则存在自然同构： 
  $
    (DD_(X\/k) cal(K))|_(X_L) cong DD_(X_L\/k_L) cal(K)|_(X_L)
  $
  对一切 $cal(K) in D^b_#[ctf] (X_et, Lambda)$ 成立。 
]
#proof[
  设 $f: X -> Spec(k), f_L: X_L -> Spec(k_L)$ 是结构态射。由前一引理，
  $
    (DD_(X\/k) cal(K))|_(X_L) &cong RHHom_Lambda (cal(K)|_(X_L), (R f^! ul(Lambda))|_(X_L)) \
    &cong RHHom_Lambda (cal(K)|_(X_L), R f_L^(!) ul(Lambda)) #[由 @base-field-extension-for-upper-shriek] \
    &cong DD_(X_L\/k_L) cal(K)|_(X_L)
  $
  至此完成。 
]*/

要继续推进，我们还需要一些极限公式。 

#lemma(name: <limit-formula-for-upper-shriek>)[
  ($R i^!$ 的极限公式) 设 $X = invlim_(i >= 0) X_i$ 是 Noether 概形，且是诸 Noether 概形在仿射过渡映射 $u_(i,j): X_i -> X_j$ 下的逆向极限。记 $u_i: X -> X_i$ 为投影。设 $h_0: Z_0 -> X_0$ 是闭浸入，经基变换得 $h_i: Z_i -> X_i$ 与 $h: Z -> X$。对任意层系统 $(cal(F)_i, phi_(i,j))$，它定义在 ${X_i}$ 上并以 $cal(F)$ 为极限层，则典范映射： 
  $
    dirlim_i (R^q h_i^! cal(F)_i)|_Z cong R^q h^! cal(F)
  $
]
#proof[
  取互补的开浸入 $g_i: U_i -> X_i$ 与 $g: U -> X$。此时 $(g_i^(-1) cal(F)_i, g_i^(-1) phi_(i,j))$ 是 ${U_i}$ 上以 $g^(-1) cal(F)$ 为极限层的层系统，故由基变换的极限公式 @limit-formula-for-base-change，有： 
  $
    u_i^(-1) R^q g_(i,*) g_i^(-1) cal(F)_i cong R^q g_* g^(-1) cal(F)
  $
  于是： 
  $
    dirlim_i (h_i^! cal(F)_i)|_Z &cong dirlim_i ker(h_i^(-1) cal(F)_i -> h_i^(-1) g_(i,*) g_i^(-1) cal(F)_i)|_Z \
    &cong ker(dirlim_i (h_i^(-1) cal(F)_i)|_Z -> dirlim_i (h_i^(-1) g_(i,*) g_i^(-1) cal(F)_i)|_Z) \
    &cong ker(h^(-1) cal(F) -> dirlim_i h^(-1) u_i^(-1) g_(i,*) g_i^(-1) cal(F)_i) \
    &cong ker(h^(-1) cal(F) -> h^(-1) g_* g^(-1) cal(F)) cong h^! cal(F)
  $
  同样地，把上述推导中所有的 $ker$ 换成 $coker$，便得到： 
  $
    dirlim_i (R^1 h_i^! cal(F)_i)|_Z cong R^1 h^! cal(F)
  $
  最后，对 $q >= 2$，有：
  $
    dirlim_i (R^q h_i^! cal(F)_i)|_Z &cong dirlim_i (h_i^(-1) R^(q-1) g_(i,*) g_i^(-1) cal(F)_i)|_Z \
    &cong dirlim_i h^(-1) u_i^(-1) R^(q-1) g_(i,*) g_i^(-1) cal(F)_i \
    &cong h^(-1) R^(q-1) g_* cal(F) cong R^q h^! cal(F)
  $
]

#lemma(name: <limit-formula-for-hom-and-ext>)[
  设 $X = invlim_(i >= 0) X_i$ 是 Noether 概形，且是诸 Noether 概形在仿射过渡映射 $u_(i,j): X_i -> X_j$ 下的逆向极限。记 $u_i: X -> X_i$ 为投影。  
  
  设 $cal(K)_0 in D^b_c ((X_0)_et, Lambda)$，$cal(K)_i = cal(K)_0|_(X_i)$，$cal(K) = cal(K)_0|_X$，并设 $(cal(G)_i, phi_(i,j))$ 是 ${X_i}$ 上以 $cal(G)$ 为极限层的层系统。则典范映射： 
  $
    dirlim_i h^q (RHom_Lambda (cal(K)_i, cal(G)_i)) -> h^q (RHom_Lambda (cal(K), cal(G))) \

    dirlim_i u_i^(-1) h^q (RHHom_Lambda (cal(K)_i, cal(G)_i)) -> h^q (RHHom_Lambda (cal(K), cal(G)))
  $
  都是同构。 

  特别地，由截断与 way-out 论证，对所有 $cal(L)_0 in D^+ ((X_0)_et, Lambda)$，其中 $cal(L)_i = cal(L)_0|_(X_i)$、$cal(L) = cal(L)_0|_X$，典范映射： 
  $
    dirlim_i h^q (RHom_Lambda (cal(K)_i, cal(L)_i)) -> h^q (RHom_Lambda (cal(K), cal(L))) \

    dirlim_i u_i^(-1) h^q (RHHom_Lambda (cal(K)_i, cal(L)_i)) -> h^q (RHHom_Lambda (cal(K), cal(L)))
  $
]
#proof[
  先验证 $RHom$ 的陈述。两边对 $cal(K)_0$ 与 $(cal(G)_i, phi_(i,j))$ 都是上同调函子。于是由 way-out 引理，只需验证 $cal(K)_0 = cal(F)_0$ 是可构造层的情形。现在取一个消解： 
  $
    dots.c -> cal(H)^((p))_0 -> dots.c -> cal(H)^((1))_0 -> cal(H)^((0))_0 -> cal(F)_0 -> 0
  $
  其中 $cal(H)^((p))_0 = j^((p))_(0,!) ul(Lambda)$，$j^((p))_0: U^((p))_0 -> X_0$ 是来自仿射概形的平展态射。于是由超上同调得到第一象限谱序列： 
  $
    E_(1,i)^(p,q) = Ext^q_Lambda (cal(H)_i^((p)), cal(G)_i) => Ext^(p+q)_Lambda (cal(F)_i, cal(G)_i)
  $
  取极限后便得到： 
  $
    E_1^(p,q) = dirlim_i Ext^q_Lambda (cal(H)_i^((p)), cal(G)_i) => dirlim_i Ext^(p+q)_Lambda (cal(F)_i, cal(G)_i)
  $
  另一方面，还有另一个谱序列： 
  $
    tilde(E)_1^(p,q) = Ext^q_Lambda (cal(H)^((p)), cal(G)) => Ext^(p+q)_Lambda (cal(F), cal(G))
  $
  比较谱序列 $E_1^(p,q)$ 与 $tilde(E)_1^(p,q)$ 可知，只需在 $cal(F)_0 = j_(0,!) ul(Lambda)$ 时证明本引理，其中 $j: U_0 -> X_0$ 是来自仿射概形的平展态射。同样地，把所有的 $Ext$ 换成 $EExt$，就应得到 $RHHom$ 的陈述。现在在这一情形下： 
  $
    dirlim_i Ext^q_Lambda (j_(i,!) ul(Lambda), cal(G)_i) cong dirlim_i H^q (U_i, cal(G)_i) cong H^q (U, cal(G)) #[由 @limit-formula-composite]
  $
  以及： 
  $
    dirlim_i EExt^q_Lambda (j_(i,!) ul(Lambda), cal(G)_i) cong dirlim_i R^q j_(i,*) j_i^(-1) cal(G)_i cong R^q j_* j^(-1) cal(G) cong EExt^q_Lambda (j_! ul(Lambda), cal(G)) #[由 @relative-limit-formula-composite] 
  $
  至此完成。 
  // $
  //   cal(S)_0 = {Z_0 subset X_0 #[closed] :& dirlim_i h^q (RHom_Lambda (cal(F)_i, cal(G)_i)) cong h^q (RHom_Lambda (cal(F), cal(G))) \
  //   & #[对一切满足 $supp(cal(F)_0) subset Z_0$ 的可构造 $cal(F)_0$] \
  //   & #[对 ${X_i}$ 上以 $cal(G)$ 为极限层的层系统 $(cal(G)_i, phi_(i,j))$]}
  // $
  // 若某个对象带下标 $0$，我们就把这个下标改成 $i$ 或直接去掉，以表示拉回到 $X_i$ 或 $X$ 的显然含义，除非另有说明。 

  // 设 $Z_0 subset X_0$ 具有这样的性质：每个真闭子集 $W_0 subset.neq Z_0$ 都在 $cal(S)_0$ 中。取浸入 $Z_0 ->^(h_0) X_0$。则对任意可构造的 $cal(F)_0$，只要 $supp(cal(F)_0) subset Z_0$，便可写成 $cal(F)_0 = h_(0,*) h_0^(-1) cal(F)_0$。取 Zariski 开集 $j_0: U_0 -> Z_0$，使 $j_0^(-1) h_0^(-1) cal(F)_0$ 是 l.c.c，再取补的闭浸入 $w_0: W_0 -> Z_0$。于是得到正合列： 
  // $
  //   0 -> h_(0,*) j_(0,!) j_0^(-1) h_0^(-1) cal(F)_0 -> cal(F)_0 -> w_(0,*) w_0^(-1) cal(F)_0 -> 0
  // $
  // 现在 $supp(w_(0,*) w_0^(-1) cal(F)_0) subset W_0 in cal(S)_0$ 已经处理过了，故只需处理第一项 $j_(0,!) j_0^(-1) h_0^(-1) cal(F)_0$。现在： 
  // $
  //   RHom_Lambda (h_(i,*) j_(i,!) j_i^(-1) h_i^(-1) cal(F)_i, cal(G)_i) cong RHom_Lambda (j_i^(-1) h_i^(-1) cal(F)_i, j_i^(-1) R h_i^! cal(G)_i)
  // $
  // 由截断与标准的 way-out 论证，要证： 
  // $
  //   dirlim_i RHom_Lambda (j_i^(-1) h_i^(-1) cal(F)_i, j_i^(-1) R h_i^! cal(G)_i) cong dirlim_i RHom_Lambda (j^(-1) h^(-1) cal(F), j^(-1) R h^! cal(G))
  // $
  // 只需证明： 
  // $
  //   dirlim_i RHom_Lambda (j_i^(-1) h_i^(-1) cal(F)_i, j_i^(-1) R^q h_i^! cal(G)_i) cong dirlim_i RHom_Lambda (j^(-1) h^(-1) cal(F), j^(-1) R^q h^! cal(G))
  // $
  // 对每个 $q$。现在由 @limit-formula-for-upper-shriek，$(R^q h_i^! cal(G)_i)$ 是 ${Z_i}$ 上以 $R^q h_i^! cal(G)$ 为极限的层系统，因此 $(j_i^(-1) R^q h_i^(-1) cal(G)_i)$ 是 $U_i$ 上以 $j^(-1) R^q h^! cal(G)$ 为极限的层系统。 
  
  // - $j_0^(-1) h_0^(-1) cal(F)_0$ 是 l.c.c. 层，且由 @limit-formula-for-upper-shriek
]

#theorem[
  设 $f: X -> Spec(k)$ 是有限型分离态射。则双对偶映射： 
  $
    cal(K) -> DD_X DD_X cal(K)
  $
  对一切 $cal(K) in D^b_#[ctf] (X_et, Lambda)$ 都是同构。 
]
#proof[
  我们对 $d = dim(X)$ 归纳。于是假定：对所有域 $k$ 与所有有限型分离的 $k$-概形 $X$，只要 $dim(X) <= d-1$，双对偶映射都是同构。 

  拉回到 $X otimes_k k^sep$ 之后验证即可。对每个有限可分扩张 $L\/k$， 
  $
    (DD_(X\/k) cal(K))|_(X_L) cong DD_(X_L\/L) (cal(K)|_(X_L))
  $
  该同构关于基变换是自然的。于是由 @limit-formula-for-hom-and-ext，对所有 $L$ 取极限，得到 
  $
    (DD_(X\/k) cal(K))|_(X_(k^sep)) cong DD_(X_(k^sep)\/k^sep) (cal(K)|_(X_(k^sep)))
  $
  因此把 $k, X$ 换成 $k^sep, X otimes_k k^sep$ 之后，不妨设 $k$ 可分闭。再由拓扑不变性，还可把 $k$ 换成 $ol(k)$，从而不妨设该域是代数闭的。 

    取紧化 $X ->^j ol(X) ->^(ol(f)) Spec(k)$。把 $ol(X)$ 换成 $X$ 的概形闭包，不妨设 $X$ 在 $ol(X)$ 中稠密，从而 $dim(ol(X)) = dim(X)$。

  对每个 $cal(L) in D^b_#[ctf] (ol(X)_et, Lambda)$，@existence-of-upper-shriek (0)(1)(3) 给出自然同构：
  $
    DD_X (j^(-1) cal(L))
    &cong RHHom_Lambda (j^(-1) cal(L), R j^! R ol(f)^! ul(Lambda)) cong RHHom_Lambda (j^(-1) cal(L), j^(-1) R ol(f)^! ul(Lambda)) \
    &cong j^(-1) RHHom_Lambda (cal(L), R ol(f)^! ul(Lambda)) = j^(-1) DD_(ol(X)) cal(L)
  $

  先取 $cal(L) = j_! cal(K)$，再取
  $cal(L) = DD_(ol(X)) j_! cal(K)$，便得到：
  $
    DD_X cal(K)
    &cong j^(-1) DD_(ol(X)) j_! cal(K), \

    DD_X j^(-1) DD_(ol(X)) j_! cal(K)
    &cong j^(-1) DD_(ol(X)) DD_(ol(X)) j_! cal(K)
  $
  从而得到等同 $DD_X DD_X cal(K) cong j^(-1) DD_(ol(X)) DD_(ol(X)) j_! cal(K)$。这些等同与双对偶相容：映射
  $
    cal(K) -> DD_X DD_X cal(K)
  $
  等同于把下式用 $j^(-1)$ 限制所得：
  $
    j_! cal(K) -> DD_(ol(X)) DD_(ol(X)) j_! cal(K).
  $
  事实上，把定义后一个映射的求值配对限制到 $X$ 上，即得此结论。由于 $j_! cal(K) in D^b_#[ctf] (ol(X)_et, Lambda)$（由 @finiteness-of-six-functors），紧合概形 $ol(X)$ 上的双对偶便推出 $X$ 上的双对偶。

  因此，要证 $DD_X$ 的双对偶，只需证 $DD_(ol(X))$ 的双对偶。于是不妨设 $X$ 在 $k$ 上紧合。固定 $cal(K) in D^b_#[ctf] (X_et, Lambda)$，作锥：
  $
    cal(K) -> DD_X DD_X cal(K) -> Delta ->^(+1)
  $
  由 @partial-biduality-in-proper-case 可见 $R Gamma(X, Delta) = 0$。我们断言 $Delta$ 的支集是 $X$ 的有限多个闭点。 

  #proof_[断言的证明][
    对仿射开集 $U subset X$，把上面的特殊三角拉回到 $U$，得到三角： 
    $
      cal(K)|_U -> DD_U DD_U cal(K)|_U -> Delta|_U ->^(+1)
    $
    于是把 $X$ 换成 $U$，不妨设 $X$ 仿射（并忘掉上面“$X$ 在 $k$ 上紧合”的假设，因为它没什么用）。取闭浸入 $i: X -> AA^m_k$，并取投影 $pi_1, dots.c, pi_m: AA^m_k -> AA^1_k$。设 $eta = Spec(k(t))$ 是 $AA^1_k$ 的泛点，$X_(eta,j) = h^(-1) (pi_j^(-1) (eta))$。则： 
    $
      dim(X_(eta,j)) <= dim(X) - 1 < d
    $
    于是可以应用归纳假设，$cal(K)|_(X_(eta,j)) -> DD_(X_(eta,j)\/k(t)) DD_(X_(eta,j)\/k(t)) cal(K)|_(X_(eta,j))$ 是同构。 

    我们断言：
    $
      (DD_X DD_X cal(K))|_(X_(eta,j)) cong DD_(X_(eta,j)\/k(t)) DD_(X_(eta,j)\/k(t)) cal(K)|_(X_(eta,j))
    $
    且与求值相容。事实上，考虑由拉回方块构成的图表： 
    // https://q.uiver.app/#r=typst&q=WzAsNyxbMCwxLCJYIl0sWzEsMSwiQUFebV9rIl0sWzIsMSwiQUFeMV9rIl0sWzMsMSwiU3BlYyhrKSJdLFsyLDAsImV0YSJdLFsxLDAsIkFBXihtLTEpX2V0YSJdLFswLDAsIlhfKGV0YSxqKSJdLFs2LDUsImknX2oiXSxbNSw0LCJwaSciXSxbMCwxLCJpIiwyXSxbMSwyLCJwaV9qIiwyXSxbMiwzXSxbNCwyLCJqIl0sWzUsMSwiaiciXSxbNiwwLCJqJyciLDJdXQ==
    #align(center, diagram({
      node((0, 1), [$X$])
      node((1, 1), [$AA^m_k$])
      node((2, 1), [$AA^1_k$])
      node((3, 1), [$Spec(k)$])
      node((2, 0), [$eta$])
      node((1, 0), [$AA^(m-1)_eta$])
      node((0, 0), [$X_(eta,j)$])
      edge((0, 0), (1, 0), [$i'_j$], label-side: left, "->")
      edge((1, 0), (2, 0), [$pi'$], label-side: left, "->")
      edge((0, 1), (1, 1), [$i$], label-side: right, "->")
      edge((1, 1), (2, 1), [$pi_j$], label-side: right, "->")
      edge((2, 1), (3, 1), "->")
      edge((2, 0), (2, 1), [$j$], label-side: left, "->")
      edge((1, 0), (1, 1), [$j'$], label-side: left, "->")
      edge((0, 0), (0, 1), [$j''$], label-side: right, "->")
    }))
    令 $g_j: X ->^i AA^m_k ->^(pi_j) AA^1_k$。则： 
    $
      DD_X cal(K) = RHHom_Lambda (cal(K), R g_j^! ul(Lambda)(1)[2])
    $
    于是由 @limit-formula-for-hom-and-ext 与 @limit-formula-for-upper-shriek，
    $
      (DD_X cal(K))|_(X_(eta,j)) cong RHHom_Lambda (cal(K)|_(X_(eta,j)), R g'_j^! ul(Lambda))(1)[2]
    $
    再对偶两次，得到典范同构 $(DD_X DD_X cal(K))|_(X_(eta,j)) cong DD_(X_(eta,j)\/k(t)) DD_(X_(eta,j)\/k(t)) cal(K)|_(X_(eta,j))$，再由归纳假设，后者又同构于 $cal(K)|_(X_(eta,j))$。特别地，$Delta|_(X_(eta,j)) = 0$。// 然而，由 @limit-formula-for-hom-and-ext， 
    // $
    //   h^q (DD_X DD_X cal(K))|_(X_(eta,j)) cong dirlim_(U subset AA^1_k) h^q (DD_X DD_X cal(K))|_(g_j^(-1) (U))
    // $
    // 作为 $AA^1_k$ 的开集上的极限。于是穿过该特殊三角， 
    // $
    //   h^q (Delta)|_(X_(eta,j)) cong dirlim_(U subset AA^1_k) h^q (Delta)|_(g_j^(-1) (U))
    // $
    现在由 @limit-formula-for-hom-and-ext，并注意 $Delta in D^b_c$， 
    $
      0 = Hom_Lambda (Delta|_(X_(eta,j)), Delta|_(X_(eta,j))) = dirlim_(U subset AA^1_k) Hom_Lambda (Delta|_(g_j^(-1)(U)), Delta|_(g_j^(-1)(U)))
    $
    其中极限取遍 $AA^1_k$ 的所有非空开集。于是右端的 $id$ 在某个更靠后的阶段必变成 $0$。但 $id$ 也必变成 $id$，所以在右端极限的某个有限阶段有 $id = 0$。因此存在稠密开集 $U_j subset AA^1_k$，使 $Delta|_(g_j^(-1)(U_j)) = 0$。 

    取 $U_1, dots.c, U_m subset AA^1_k$，对每个 $j = 1,dots.c,m$ 都这样选取。则： 
    $
      Delta|_(union.big_(j=1)^m g_j^(-1)(U_j)) = 0
    $
    现在：
    $
      X - union.big_(j=1)^m g_j^(-1)(U_j) &= i^(-1) (AA^m_k - union.big_(j=1)^m pi_j^(-1) (U_j)) \
      &= i^(-1) ((AA^1_k - U_1) times_k dots.c times_k (AA^1_k - U_m))
    $
    然而每个 $AA^1_k - U_j$ 都只是有限多个形如 $Spec(k)$ 的闭点。于是 $X - union.big_(j=1)^m g_j^(-1)(U_j)$ 也只是有限多个形如 $Spec(k)$ 的闭点，故 $Delta$ 的支集是有限多个闭点。 
  ]
  现在 $Delta$ 的支集是有限多个闭点 $x_1, dots.c, x_m in X$，它们都同构于 $Spec(k)$。于是： 
  $
    Delta = oplus.big_(j=1)^m x_(j,*) M_j
  $
  其中 $M_j in D((x_j)_et, Lambda) cong D(Lambda)$ 是复形。但我们已看到 $0 = R Gamma(X, Delta)$，所以： 
  $
    0 = R Gamma(X, Delta) = oplus.big_(j=1)^m M_j
  $
  因此每个 $M_j = 0$ 都成立，从而 $Delta = 0$。这就证明了 $cal(K) -> DD_X DD_X cal(K)$ 是同构。 
]

总结一下上述讨论： 

#theorem(name: <verdier-duality>)[
  (Verdier 对偶) 对任意域 $k$ 与任意 $n$-挠 Noether 环 $Lambda$（其中 $n in k^times$），对每个 $X$，只要它在 $k$ 上有限型分离， 
  $
    DD_X = DD_(X\/k): D^b_#[ctf] (X_et, Lambda)^opp &-> D^b_#[ctf] (X_et, Lambda) \
    
    cal(K) &|-> RHHom_Lambda (cal(K), R f^! Lambda)
  $
  双对偶映射 $cal(K) ->^tilde DD_X DD_X cal(K)$ 使对偶复形函子成为一个反变对合。对任意态射 $f: X -> Y$，其中两端都是有限型分离的 $k$-概形，我们有自然等同： 
  $
    DD_Y compose R f_* cong R f_! compose DD_X \
    DD_Y compose R f_! cong R f_* compose DD_X \
    DD_X compose f^(-1) cong R f^! compose DD_Y \
    DD_X compose R f^! cong f^(-1) compose DD_Y
  $
  以上都在 $D^b_#[ctf]$ 上成立。 
]
#proof[
  对合部分已在前一个定理中证明。至于四个等式，
  $
    DD_Y compose R f_! cong R f_* compose DD_X
  $
  是形式性的，正是 @existence-of-upper-shriek (4)。陈述 $DD_Y compose R f_* cong R f_! compose DD_X$ 于是由双对偶推出。剩下关于 $f^(-1), R f^!$ 的两条陈述，则由已证的两条关于 $R f_*, R f_!$ 的陈述经伴随得到。 
]
