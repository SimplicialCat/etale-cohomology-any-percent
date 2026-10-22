#import "void-import.typ": *

== 导出范畴中的陈述

导出范畴是一套抽象机制，它让导出函子的概念变得更自然。某种意义上，导出范畴正是导出函子天然的栖身之所。 

后面各节以及更往后的内容，我们会依次讨论： 

- 紧合基变换
- 紧支推前 (pushforward with proper support)
- 局部零调性 (local acyclicity)
- 投影公式与 Künneth 公式
- Poincaré 对偶

它们在各自的陈述中都大量用到导出范畴，有时这种使用甚至是本质性的。因此，简要介绍导出范畴，并把本章先前的一些结果改写成导出范畴中的陈述，是免不了的。这一插曲小节的作用正在于此。 

我们不构造同伦范畴与导出范畴，也不构造抽象的三角范畴、导出函子与 t-结构。关于导出范畴和导出函子的定义，请读者参阅标准材料，例如： 

- @cite-hartshorne-rd 第 I 章；
- @cite-Wei94 第 10 章；
- @cite-Lip60 第 I 章。

凡是翻译需要的构造，我们大多只作粗略讨论，而不给出冗长的严格证明。 

不过，有一个重要的引理我们往后会反复用到，所以现在就陈述出来： 

#definition(name: <defn-cohomological-dimension>)[
  设 $F: cal(D) -> cal(C)$ 是两个带 t-结构的三角范畴之间的三角函子，$F$ 的有界性定义如下： 

  - 若存在 $m$，使得 $F(cal(D)_(<=n)) subset cal(C)_(<=n+m)$，则称 $F$ 是*上有界* (bounded above) 的； 

  - 若存在 $m$，使得 $F(cal(D)_(>=n)) subset cal(C)_(>=n-m)$，则称 $F$ 是*下有界* (bounded below) 的。 

  在这些情形下，把满足相应性质的最小整数 $m$ 分别称为 $F$ 的*上方*上同调维数 (cohomological dimension) 与*下方*上同调维数。 
]

#lemma[
  (way-out 引理) 设 $cal(A), cal(B)$ 是两个 Abel 范畴，$cal(A)'$ 是 $cal(A)$ 的厚子范畴，$D^bullet_(cal(A)') (cal(A))$ 是 $D^bullet (cal(A))$ 的三角子范畴，由那些上同调属于 $cal(A)'$ 的复形组成，其中 $bullet in {#`blank`, +, -, b}$。假设有两个三角函子： 
  $
    F, G: D^bullet_(cal(A)') (cal(A)) -> D(cal(B))
  $
  以及自然变换 $eta: F -> G$。又设对任意 $X in cal(A)'$，把它视为 $D^bullet_(cal(A)') (cal(A))$ 中的对象时，$eta_X: F(X) -> G(X)$ 都是同构，并且下列条件之一成立： 

  + $bullet = b$； 
  + $bullet = +$，且 $F,G$ 下有界； 
  + $bullet = -$，且 $F,G$ 上有界； 
  + $bullet = #`blank`$，且 $F,G$ 上有界且下有界。 

  则 $eta$ 是自然同构。 
]

我们先来定义平展层的导出范畴。 

#notation(name: <derived-categories-of-etale-sheaves>)[
  设 $Lambda$ 是环。则平展 $Lambda$-模层构成的范畴 $cAb(X_et, Lambda)$ 是 Grothendieck 范畴，即满足 (Ab5) 且有生成元的 Abel 范畴。 

  在 @ab-x-et-the-abelian-cat 中，我们已经证明 $cAb(X_et)$ 满足 (Ab5)，并且有生成元 $G$。 
  
  - 遗忘函子 $cAb(X_et, Lambda) -> cAb(X_et)$ 正合且保守（这实际上只是说：$Lambda$-模层构成的序列正合，当且仅当它作为交换群层序列正合），因此 $cAb(X_et, Lambda)$ 满足 (Ab5)。 
  
  - 取 $cAb(X_et)$ 的一个生成元 $G$。由 Hom-张量伴随，有： 
    $
      Hom_Lambda (G otimes_ZZ Lambda, -) = Hom_ZZ (G, -): cAb(X_et, Lambda) -> cAb
    $
    该函子忠实，因为 $G$ 是 $cAb(X_et, Lambda)$ 的生成元。因此 $G otimes_ZZ Lambda$ 是 $cAb(X_et, Lambda)$ 的生成元。 
  
  于是 $cAb(X_et, Lambda)$ 确实是 Grothendieck 范畴。 

  我们定义如下三角范畴： 

  - 对 $bullet in {#`blank`, -, +, b}$，$D^bullet (X_et, Lambda)$ 指 $cAb(X_et, Lambda)$ 的导出范畴，并依次由全体复形、上有界复形、下有界复形与有界复形构成。 

  挠层给出 $cAb(X_et, Lambda)$ 的一个厚子范畴。给定层的一个扩张： 
  $
    cal(F) -> cal(G) -> cal(H)
  $
  由 @torsion-sheaves-first-props (3) 可知，若 $cal(F)$ 与 $cal(H)$ 是挠层，则 $cal(G)$ 也是挠层。 

  于是，由 $cAb(X_et, Lambda)$ 中全体挠层构成的 $cAb_#[tor] (X_et, Lambda)$ 是 $cAb(X_et, Lambda)$ 的一个厚子范畴。 

  因此，对 $bullet in {#`blank`, -, +, b}$，$D^bullet_#[tor] (X_et, Lambda)$ 是 $D^bullet (X_et, Lambda)$ 的三角子范畴。 

  回忆一下：我们已经论证过 $cAb(X_et, Lambda)$ 是 Grothendieck 范畴。因此，无界导出范畴 $D(X_et, Lambda)$ 中的每个复形都拟同构于一个由内射对象组成的 K-内射复形（见 #cite-stacks("079P", [Theorem 19.12.6])）。于是，从 $cAb(X_et, Lambda)$ 出发的任意左正合函子都有右导出函子，而且不仅在下有界导出范畴 $D^+ (X_et, Lambda)$ 上有定义，在无界导出范畴 $D(X_et, Lambda)$ 上也有定义。#footnote[我们最终陈述投影公式与 Künneth 公式时，这一推广必不可少：那里同时涉及（右）导出推前与（左）导出张量。张量只对 $D^-$ 定义，因此我们必须能够对 $D^-$ 中的复形施加右导出函子。]

  /*于是我们有函子： 
  $
    R Gamma(U, -): D(X_et, Lambda) -> D(Lambda) \
    R f_*: D(X_et, Lambda) -> D(Y_et, Lambda) \
    RHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(Lambda) \
    RHHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(X_et, Lambda)
  $
  它们都作为导出函子得到。 

  有一个函子需要取左导出：张量积。层范畴没有足够多的投射对象，但有足够多的平坦对象（见 @flat-resolution-of-et-sheaf）。这使得我们能在上有界导出范畴上作出左导出张量积： 
  $
    - Lotimes_Lambda -: D^- (X_et, Lambda) times D^- (X_et, Lambda) -> D^- (X_et, Lambda)
  $
  要在无界导出范畴上定义它，需要用 K-平坦复形，也就是与正合复形作张量积后仍然正合的复形。K-平坦消解的存在性归功于 #cite-stacks("06YS")[Lemma 21.17.11]。 */
]

/*
再做一步，我们给出一个更一般的抽象注记： 
#remark[
  还有一个抽象构造我们会经常用到，那就是 Grothendieck–Leray 谱序列的翻译。回忆：设左正合函子 
  $
    cal(A) ->^F cal(B) ->^G cal(C)
  $
  定义在 Abel 范畴之间，$cal(A)$ 与 $cal(B)$ 都有足够多的内射对象，且 $F$ 把 $cal(A)$ 中的内射对象送到 $cal(B)$ 中的 $G$-零调对象。则 Grothendieck–Leray 谱序列给出自然的谱序列： 
  $
    E_2^(p,q) = R^p G (R^q F (X)) ==> R^(p+q) (G compose F) (X)
  $
  在导出范畴里，这个陈述的形式要干净得多，就是： 
  $
    R G compose R F cong R (G compose F): D^+ (cal(A)) -> D^+ (cal(C))
  $
  现在假设 $cal(A), cal(B)$ 是 Grothendieck 范畴，于是 $D(cal(A)), D(cal(B))$ 中的每个复形都可以（函子性地）被 K-内射复形消解，右导出函子也就在无界导出范畴上有定义。这时，$F$ 把内射对象送到 $G$-零调对象已经不足以保证： 
  $
    R G compose R F cong R (G compose F): D(cal(A)) -> D(cal(C))
  $
  取而代之的要求是：逐项作用 $F$ 把 K-内射复形送到 K-$G$-零调复形。 

  对我们的研究最重要的情形，是 $F$ 具有正合左伴随 $L$ 的情形。此时，对任意 K-内射复形 $M^bullet in K(cal(A))$ 与任意正合复形 $N^bullet in K(cal(B))$： 
  $
    Hom_(K(cal(B))) (N^bullet, F(M^bullet)) = Hom_(K(cal(A))) (L(N^bullet), M^bullet) = 0
  $
  因为 $L$ 与 $N^bullet$ 都正合，所以 $L(N^bullet)$ 正合，而 $M^bullet$ 是 K-内射的。于是 $F(M^bullet)$ 是 K-内射的，从而 $F$ 保持 K-内射复形。 
]*/

下面我们开始把 @sect-ab-x-et-as-abelian-cat、@sect-functoriality-of-etale-topos、@sect-open-closed 与 @sect-hom-tensor 中关于我们已构造的各种函子的结果，翻译成导出范畴的语言。 

#properties(name: <derived-functoriality-etale>)[
  (平展意象的导出函子性)

  设 $X, Y, Z$ 是概形，$f: X -> Y, g: Y -> Z$ 是概形态射，$Lambda$ 是系数环。则： 

  + （函子性）存在三角函子：#h(1fr)
    $
      R f_*: D(X_et, Lambda) -> D(Y_et, Lambda) \
      f^(-1): D(Y_et, Lambda) -> D(X_et, Lambda) \
      - Lotimes_Lambda -: D(X_et, Lambda) times D(X_et, Lambda) -> D(X_et, Lambda) \
      RHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(Lambda) \
      RHHom_Lambda (-, -): D(X_et, Lambda)^opp times D(X_et, Lambda) -> D(X_et, Lambda) \
      R Gamma(U, -): D(X_et, Lambda) -> D(Lambda), forall U in Et_X
    $
    其中 $f^(-1)$ 逐项作用，$Lotimes_Lambda$ 是 $otimes_Lambda$ 的左导出函子（并且是对称幺半的），其余函子都取右导出。 

    对平展态射 $j: U -> X$ 与闭浸入 $i: Z -> X$，同样有三角函子： 
    $
      j_!: D(U_et, Lambda) -> D(X_et, Lambda) \
      R i^!: D(X_et, Lambda) -> D(Z_et, Lambda)
    $
    其中 $j_!$ 逐项作用，$R i^!$ 取右导出。 

  + （伴随）这些函子有如下伴随对： 

    + #h(1fr)
      $
        f^(-1) tack.l R f_*
      $
    
    + 对平展的 $j$ 与闭浸入 $i$： 
      $
        j_! tack.l j^(-1) \
        i_* tack.l R i^!
      $

    + （Hom-张量对偶）对任意 $cal(K) in D(X_et, Lambda)$： 
      $
        - Lotimes_Lambda cal(K) tack.l RHHom_Lambda (cal(K), -) 
      $

  + （内伴随）存在典范拟同构： 

    + #h(1fr)
      $
        RHHom_Lambda (cal(K), R f_* cal(L)) ->^tilde R f_* RHHom_Lambda (f^(-1) cal(K), cal(L))
      $

    + 
      $
        RHHom_Lambda (cal(K) Lotimes_Lambda cal(L), cal(M)) ->^tilde RHHom_Lambda (cal(K), RHHom_Lambda (cal(L), cal(M)))
      $

    + 对平展态射 $j: U -> X$ 与闭浸入 $i: Z -> X$： 
      $
        RHHom_Lambda (j_! cal(K), cal(L)) ->^tilde R j_* RHHom_Lambda (cal(K), j^(-1) cal(L)) \

        RHHom_Lambda (i_* cal(K), cal(L)) ->^tilde i_* RHHom_Lambda (cal(K), R i^! cal(L))
      $
    
    只要把最外层的 $RHHom_Lambda$（或 $R f_* RHHom_Lambda$）换成 $RHom_Lambda$，上述所有拟同构都成立。 

  + （幺半恒等式）存在典范拟同构： 

    + （$f^(-1)$ 是幺半的）#h(1fr)
      $
        f^(-1) cal(K) Lotimes_Lambda f^(-1) cal(L) ->^tilde f^(-1) (cal(K) Lotimes_Lambda cal(L))
      $

    + （投影公式）若 $f$ 平展，
      $
        f_! (f^(-1) cal(L) Lotimes_Lambda cal(K)) ->^tilde cal(L) Lotimes_Lambda f_! cal(K)
      $

  + （导出函子的复合）
    
    + （Leray 谱序列）#h(1fr)
      $
        R g_* compose R f_* cong R(g compose f)_*
      $
      对 $V in Et_Y$， 
      $
        R Gamma(V, R f_* (-)) cong R Gamma(V times_Y X, -)
      $

    + 
      $
        f^(-1) compose g^(-1) cong (g compose f)^(-1)
      $

    + 对平展态射 $U ->^j V ->^f X$ 与闭浸入 $W ->^i Z ->^k X$， 
      $
        (f compose j)_! = f_! compose j_!, R(k compose i)^! = R i^! compose R k^!
      $
    
    + 在 $D(X_et)$ 上， 
      $
        RHom_Lambda (-, -) cong R Gamma(X, RHHom_Lambda (-, -))
      $

  + （开闭三角）对闭浸入 $i: Z -> X$ 与其互补的开浸入 $j: U -> X$，存在典范的特殊三角： 
    + （零延拓三角）#h(1fr)
      $
        j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1) \
      $
    + （带支集截面三角）#h(1fr)
      $
        i_* R i^! cal(K) -> cal(K) -> R j_* j^(-1) cal(K) ->^(+1)
      $
]
#proof[
  (1) 这些函子当中，$R f_*, RHom_Lambda, RHHom_Lambda, R Gamma(U, -), R i^!$ 都可以像前面讨论的那样，用 K-内射消解定义为右导出函子。$j_!$ 与 $f^(-1)$ 正合，因此可以逐项作用。唯一需要稍作说明的函子是 $Lotimes_Lambda$。为此我们要证明：$D(X_et, Lambda)$ 中任意（可能无界的）复形都可以换成 K-平坦复形。做法是取它与自身的上有界截断的极限，见 #cite-stacks("06YS")[Lemma 21.17.11]；该结果告诉我们，$D(X_et, Lambda)$ 中每个复形都有从一个由平坦对象组成的 K-平坦复形到它的逐项满射拟同构。 

  (2) 这些伴随关系来自 Abel 范畴上相应的伴随对，即： 

  - $f^(-1) tack.l f_*$：@pullback-first-props (1)； 
  - $j_! tack.l j^(-1)$：@etale-lower-shriek-first-props (1)； 
  - $i_* tack.l i^!$：@closed-immersion-upper-shriek-first-props (1)； 
  // - Hom-张量：@hom-tensor-first-props (1)； 

  再加上一个关于导出函子如何与伴随相互作用的抽象结果：#cite-stacks("09T5")[Lemma 13.30.3]。 

  至于 Hom-张量，我们需要稍微小心一点。 

  #lemma(name: <hhom-from-kflat-to-kinj-is-kinj>)[
    设 $cal(P) in K(X_et, Lambda)$ 是 K-平坦复形，$cal(I) in K(X_et, Lambda)$ 是 K-内射复形。则 $RHHom_Lambda (cal(P), cal(I)) in K(X_et, Lambda)$ 是 K-内射的。 
  ]
  #proof[
    取任意正合复形 $cal(K) in K(X_et, Lambda)$。此时： 
    $
      Hom_K (cal(K), RHHom_Lambda (cal(P), cal(I))) = Hom_K (cal(K) otimes_Lambda cal(P), cal(I)) = 0
    $
    其中 $cal(K) otimes_Lambda cal(P)$ 正合，因为 $cal(K)$ 正合且 $cal(P)$ 是 K-平坦的；最后一个 Hom 为零，因为 $cal(I)$ 是 K-内射的。 
  ]

  现在要证明： 
  $
    Hom_D (cal(K) Lotimes_Lambda cal(L), cal(M)) = Hom_D (cal(K), RHHom_Lambda (cal(L), cal(M)))
  $
  我们把 $cal(L)$ 换成拟同构的 K-平坦复形 $cal(P)$，把 $cal(M)$ 换成拟同构的 K-内射复形 $cal(I)$。于是需要证明： 
  $
    Hom_D (cal(K) otimes_Lambda cal(P), cal(I)) = Hom_D (cal(K), HHom_Lambda (cal(P), cal(I)))
  $
  然而，由上一个引理，$cal(I)$ 与 $HHom_Lambda (cal(P), cal(I))$ 都是 K-内射的；而对 K-内射的 $cal(I)$，有 $Hom_D (-, cal(I)) = Hom_K (-, cal(I))$。因此只需证明： 
  $
    Hom_K (cal(K) otimes_Lambda cal(P), cal(I)) = Hom_K (cal(K), HHom_Lambda (cal(P), cal(I)))
  $
  而这不过是 Hom-张量对偶的直接推论。 

  (5)
  #remark[
    回忆：设左正合函子 
    $
      cal(A) ->^F cal(B) ->^G cal(C)
    $
    定义在 Abel 范畴之间，$cal(A)$ 与 $cal(B)$ 都有足够多的内射对象，且 $F$ 把 $cal(A)$ 中的内射对象送到 $cal(B)$ 中的 $G$-零调对象。则 Grothendieck–Leray 谱序列给出自然的谱序列： 
    $
      E_2^(p,q) = R^p G (R^q F (X)) ==> R^(p+q) (G compose F) (X)
    $
    在导出范畴里，这个陈述的形式要干净得多，就是： 
    $
      R G compose R F cong R (G compose F): D^+ (cal(A)) -> D^+ (cal(C))
    $
    现在假设 $cal(A), cal(B)$ 是 Grothendieck 范畴，于是 $D(cal(A)), D(cal(B))$ 中的每个复形都可以（函子性地）被 K-内射复形消解，右导出函子也就在无界导出范畴上有定义。这时，$F$ 把内射对象送到 $G$-零调对象已经不足以保证： 
    $
      R G compose R F cong R (G compose F): D(cal(A)) -> D(cal(C))
    $
    取而代之，我们要求 $F$ 逐项作用时把 K-内射复形送到 K-$G$-零调复形。 

    对我们的研究最重要的情形，是 $F$ 具有正合左伴随 $L$ 的情形。此时，对任意 K-内射复形 $M^bullet in K(cal(A))$ 与任意正合复形 $N^bullet in K(cal(B))$： 
    $
      Hom_(K(cal(B))) (N^bullet, F(M^bullet)) = Hom_(K(cal(A))) (L(N^bullet), M^bullet) = 0
    $
    因为 $L$ 与 $N^bullet$ 都正合，所以 $L(N^bullet)$ 正合，而 $M^bullet$ 是 K-内射的。于是 $F(M^bullet)$ 是 K-内射的，从而 $F$ 保持 K-内射复形。 
  ]

  这个注处理的情形涵盖了 (5) 中的大部分，即 $f_*$（其正合左伴随为 $f^(-1)$）与 $i^!$（其正合左伴随为 $i_*$）。(5) 中涉及正合函子的恒等式由逐项作用得到。于是立刻得到 (5a)(5b)(5c)。至于 (5d)，为证明： 
  $
    RHom_Lambda (cal(K), cal(L)) = R Gamma(X, RHHom_Lambda (cal(K), cal(L)))
  $
  我们把 $cal(K)$ 换成拟同构的 K-平坦复形 $cal(P)$，把 $cal(L)$ 换成拟同构的 K-内射复形 $cal(I)$。此时： 
  $
    R Gamma(X, RHHom_Lambda (cal(K), cal(L))) &= R Gamma(X, HHom_Lambda (cal(P), cal(I))) \
    &= Gamma(X, HHom_Lambda (cal(P), cal(I))) #[因为 $HHom_Lambda (cal(P), cal(I)) $ 是 K-内射的] \
    &= Hom_Lambda (cal(P), cal(I)) = RHom_Lambda (cal(K), cal(L))
  $

  至于 (3)，只需证明 $RHHom$ 版本，因为 $RHom$ 版本可对两边作用 $R Gamma(X, -)$，再利用 (5a)(5d) 得到。 

  (3b) 的证明与 (2c) 相同：把 $cal(L)$ 换成拟同构的 K-平坦复形 $cal(P)$，把 $cal(M)$ 换成拟同构的 K-内射复形 $cal(I)$，于是： 
  $
    RHHom_Lambda (cal(K) Lotimes_Lambda cal(L), cal(M)) &= HHom_Lambda (cal(K) otimes_Lambda cal(P), cal(I)) = HHom_Lambda (cal(K), HHom_Lambda (cal(P), cal(I))) \
    &= RHHom_Lambda (cal(K), HHom_Lambda (cal(P), cal(I))) #[因为 $HHom_Lambda (cal(P), cal(I)) $ 是 K-内射的] \
    &= RHHom_Lambda (cal(K), RHHom_Lambda (cal(L), cal(M)))
  $

  对 (3a) 与 (3c)，注意： 

  #lemma[
    设 $cal(K) -> cal(L)$ 是 $D(X_et, Lambda)$ 中的态射。它是拟同构，当且仅当对每个 $U in Et_X$， 
    $
      R Gamma(U, cal(K)) -> R Gamma(U, cal(L))
    $
    都是拟同构。 
  ]
  #proof[
    正向蕴含显然。反之，假设上述态射对所有 $U$ 都是拟同构。取拟同构的 K-内射消解 $cal(K) -> cal(I), cal(L) -> cal(J)$。由于 $cal(J)$ 是 K-内射的，有 $Hom_K (cal(K), cal(J)) = Hom_K (cal(I), cal(J))$，所以 $cal(K) -> cal(L)$ 提升为态射 $cal(I) -> cal(J)$。于是下面这些态射 
    $
      Gamma(U, cal(I)) -> Gamma(U, cal(J))
    $
    即 $h^q (R Gamma(U, cal(I))) ->^tilde h^q (R Gamma(U, cal(J)))$，亦即 $Gamma(U, h^q (cal(I))) ->^tilde Gamma(U, h^q (cal(J)))$。因此 $h^q (cal(I)) -> h^q (cal(J))$ 都是同构，即 $cal(I) -> cal(J)$ 是拟同构。 
  ]
  注意 $R f_*, j_!, R i^!$ 与 $RHHom$ 都与平展基变换交换。由 (5d)，$R Gamma(U, RHHom_Lambda (cal(K), cal(L))) = RHom_Lambda (cal(K)|_U, cal(L)|_U)$。因此只需证明 (3a)(3c) 的 $RHom$ 版本。此时： 
  $
    h^q (RHom_Lambda (cal(K), cal(L))) = Hom_(D(X_et,Lambda)) (cal(K), cal(L)[q])
  $
  所以要证这些拟同构，可以把 $RHom_Lambda$ 换成 $Hom_D$，再由 (1) 得出结论。 

  至于 (4)，可由 (3) 形式地推出。事实上，对 (4a)： 
  $
    Hom_D (f^(-1) cal(K) Lotimes_Lambda f^(-1) cal(L), cal(M)) &= Hom_D (f^(-1) cal(K), RHHom(f^(-1) cal(L), cal(M))) \
    &= Hom_D (cal(K), R f_* RHHom(f^(-1) cal(L), cal(M))) \
    &= Hom_D (cal(K), RHHom(cal(L), R f_* cal(M))) #[由 (3a)] \
    &= Hom_D (cal(K) Lotimes_Lambda cal(L), R f_* cal(M)) \
    &= Hom_D (f^(-1) (cal(K) Lotimes_Lambda cal(L)), cal(M))
  $

  对 (4b)： 
  $
    Hom_D (f_! (cal(K) Lotimes_Lambda f^(-1) cal(L)), cal(M)) &= Hom_D (cal(K) Lotimes_Lambda f^(-1) cal(L), f^(-1) cal(M)) \
    &= Hom_D (f^(-1) cal(L), RHHom_Lambda (cal(K), f^(-1) cal(M))) \
    &= Hom_D (cal(L), R f_* RHHom_Lambda (cal(K), f^(-1) cal(M))) \
    &= Hom_D (cal(L), RHHom_Lambda (f_! cal(K), cal(M))) \
    &= Hom_D (f_! cal(K) Lotimes_Lambda cal(L), cal(M))
  $

  (6) 先看 (6a) 的零延拓三角： 
  $
    j_! j^(-1) cal(K) -> cal(K) -> i_* i^(-1) cal(K) ->^(+1)
  $
  由于所涉函子都逐项作用，由 @etale-lower-shriek-first-props (3) 即得。对 (6b)，我们把 $cal(K)$ 换成拟同构的 K-内射复形 $cal(I)$，其分量都是内射对象，并要证明存在特殊三角： 
  $
    i_* i^! cal(I) -> cal(I) -> j_* j^(-1) cal(I) ->^(+1)
  $
  为此只需证明：对任意内射对象 $cal(J) in cAb(X_et, Lambda)$，都有正合列： 
  $
    0 -> i_* i^! cal(J) -> cal(J) -> j_* j^(-1) cal(J) -> 0
  $
  由 @closed-immersion-upper-shriek-first-props (0)，这个序列左正合，因此只需证明 $cal(J) -> j_* j^(-1) cal(J)$ 是满射。于是只需证明：对每个 $V in Et_X$，$cal(J)(V) -> cal(J)(U times_X V)$ 都是满射。设 $g: V -> X$ 与 $g_U: U times_X V -> U -> X$，于是 $g_(U,!) ul(Lambda) -> g_! ul(Lambda)$ 是单射。由于 $cal(J) in cAb(X_et, Lambda)$ 是内射对象， 
  $
    Hom_Lambda (g_! ul(Lambda), cal(J)) ->> Hom_Lambda (g_(U,!) ul(Lambda), cal(J))
  $
  是满射，即 $cal(J)(V) -> cal(J)(U times_X V)$ 是满射。证毕。 
]

#remark[
  还有一个相容性结果需要确立。$R f_*$ 与 $R Gamma(U, -)$ 都有两种定义方式。以 $R f_*$ 为例： 

  - 直接作为 $f_*: cAb(X_et, Lambda) -> cAb(Y_et, Lambda)$ 的右导出函子； 

  - 先经遗忘函子看成交换群层，再对 $f_*: cAb(X_et) -> cAb(Y_et)$ 取右导出，最后借函子性赋予 $Lambda$-模结构。 

  这两种做法为什么交换？换言之，为什么下面这些图表都交换？ 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFhfZXQsIExhbWJkYSkiXSxbMCwxLCJEKFhfZXQpIl0sWzEsMCwiRChMYW1iZGEpIl0sWzEsMSwiRChaWikiXSxbMSwzLCJSIEdhbW1hXlpaIChVLCAtKSIsMl0sWzAsMiwiUiBHYW1tYV5MYW1iZGEgKFUsIC0pIl0sWzAsMSwiaW90YSIsMl0sWzIsMywiaW90YSJdXQ==
  #align(center, diagram({
    node((-1, -1), [$D(X_et, Lambda)$])
    node((-1, 0), [$D(X_et)$])
    node((0, -1), [$D(Lambda)$])
    node((0, 0), [$D(ZZ)$])
    edge((-1, 0), (0, 0), [$R Gamma^ZZ (U, -)$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$R Gamma^Lambda (U, -)$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$iota$], label-side: right, "->")
    edge((0, -1), (0, 0), [$iota$], label-side: left, "->")
  }))
  以及： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJEKFhfZXQsIExhbWJkYSkiXSxbMCwxLCJEKFhfZXQpIl0sWzEsMCwiRChZX2V0LCBMYW1iZGEpIl0sWzEsMSwiRChZX2V0KSJdLFsxLDMsIlIgZl5aWl8qIiwyXSxbMCwyLCJSIGZfKl5MYW1iZGEiXSxbMCwxLCJpb3RhIiwyXSxbMiwzLCJpb3RhIl1d
  #align(center, diagram({
    node((-1, -1), [$D(X_et, Lambda)$])
    node((-1, 0), [$D(X_et)$])
    node((0, -1), [$D(Y_et, Lambda)$])
    node((0, 0), [$D(Y_et)$])
    edge((-1, 0), (0, 0), [$R f^ZZ_*$], label-side: right, "->")
    edge((-1, -1), (0, -1), [$R f_*^Lambda$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$iota$], label-side: right, "->")
    edge((0, -1), (0, 0), [$iota$], label-side: left, "->")
  }))
  （其中 $iota$ 是遗忘函子。） 

  遗忘函子 $iota$ 有左伴随 $ul(Lambda) Lotimes_ZZ -$。于是 
  $
    iota compose R f^Lambda_* tack ul(Lambda) Lotimes_ZZ f_ZZ^(-1) (-)
  $
  而另一方面，
  $
    R f_*^ZZ compose iota tack f_ZZ^(-1) (ul(Lambda) Lotimes_ZZ -)
  $
  由 @derived-functoriality-etale (4a) 可知，这两个左伴随相同。因此有自然同构 $iota compose R f^Lambda_* cong R f_*^ZZ compose iota$。 

  类似地，设 $g: U -> X$。$R Gamma(U, -): D(X_et, Lambda) -> D(Lambda)$ 有左伴随 $g_! compose a_X$，其中 $a_X: D(Lambda) -> D(X_et, Lambda)$ 是常值层函子。于是 
  $
    iota compose R Gamma^Lambda (U, -) tack g_! a_X (Lambda Lotimes_ZZ -)
  $
  而另一方面，
  $
    R Gamma^ZZ (U, -) compose iota tack ul(Lambda) Lotimes_ZZ g_! a_X (-)
  $
  由 @derived-functoriality-etale (4b) 可知，这两个左伴随相同。因此有自然同构 $iota compose R Gamma^Lambda (U, -) cong R Gamma^ZZ (U, -) compose iota$。 
]

因此，我们可以放心地把交换群层上导出函子的各种性质搬到带系数的导出范畴上。/*首先来处理定义在 @sect-functoriality-of-etale-topos 中的 $Gamma, f_*$ 与 $f^(-1)$： 

#construction[
  设 $f: X -> Y$ 是概形态射。 

  + $f^(-1): cAb(Y_et, Lambda) -> cAb(X_et, Lambda)$ 提升为三角函子：#h(1fr)
    $
      f^(-1): D^bullet (Y_et, Lambda) -> D^bullet (X_et, Lambda)
    $
    其中 $bullet in {#`blank`, -, +, b}$，做法是逐项把 $f^(-1)$ 作用于复形。 

  + $f_*: cAb(X_et, Lambda) -> cAb(Y_et, Lambda)$ 提升为三角函子：#h(1fr)
    $
      R f_*: D^bullet (X_et, Lambda) -> D^bullet (Y_et, Lambda)
    $
    其中 $bullet in {#`blank`, +}$，作为 $f_*$ 的导出函子。 

    此外，$f^(-1): D^bullet (Y_et, Lambda) arrows.rl D^bullet (X_et, Lambda)$ 构成伴随对。 

  + 对 $U in Et_X$，$Gamma(U, -): cAb(X_et, Lambda) -> AMod(Lambda)$ 提升为三角函子：#h(1fr)
    $
      R Gamma(U, -): D^bullet (X_et, Lambda) -> D^bullet (Lambda)
    $
    其中 $bullet in {#`blank`, +}$，作为 $Gamma(U, -)$ 的导出函子。 

  #properties[
    对概形态射 $X ->^f Y ->^g Z$，有三角函子的自然同构： 
    $
      R(g compose f)_* = R g_* compose R f_*: D^bullet (X_et, Lambda) -> D^bullet (Z_et, Lambda)
    $
    以及： 
    $
      R Gamma(Y, -) compose R f_* = R Gamma(X, -): D^bullet (X_et, Lambda) -> D^bullet (Lambda)
    $
    其中 $bullet in {#`blank`, +}$。 
  ]
]*/

接下来，我们翻译 @sect-stalks 中关于茎的理论。 

#properties[
  对 $X$ 的任意几何点 $ol(x)$，在复形上逐项取茎给出三角函子： 
  $
    (-)_(ol(x)): D(X_et, Lambda) -> D (Lambda)
  $
  此外，下列条件等价： 
  #[
    #set enum(numbering: "(a)")
    + #h(1fr)
      $
        cal(K) -> cal(L)
      $
      在 $D(X_et, Lambda)$ 中是拟同构。 

    + 对 $X$ 的所有几何点 $ol(x)$， 
      $
        cal(K)_(ol(x)) -> cal(L)_(ol(x))
      $
      在 $D(Lambda)$ 中都是拟同构。 

    + 存在子集 $E subset X$，它与 $X$ 的每个非空局部闭子集都相交；并且对每个 $x in E$，都有 $X$ 的某个位于 $x$ 上方的几何点 $ol(x)$，使得： 
      $
        cal(K)_(ol(x)) -> cal(L)_(ol(x))
      $
      在 $D(Lambda)$ 中是拟同构。 
  ]
]
#proof[
  只需把 @stalks-detects-properties 应用于上同调群上的态射。 
]

接下来，
