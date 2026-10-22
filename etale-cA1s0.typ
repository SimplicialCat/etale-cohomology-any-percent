// audit-exception: 公式中作为文字条件的 #[affine] 文本块已译为“仿射”，其余公式逐字未动。
#import "void-import.typ": *

极限论证是一种技巧，用来把关于一般拟紧拟分离概形的命题归约到关于 Noether 概形的命题。若在最一般的形式下陈述，它还能用于其他目的，例如把局部环上的性质铺开到开邻域上。 

这一手法的直观如下：给定仿射概形 $X = Spec(A)$，$A$ 的每个元素都包含在 $A$ 的某个 $ZZ$ 上有限型子环里。换言之，把 $A$ 的所有 $ZZ$ 上有限型子环按包含排成正向集，记为 ${A_lambda}_lambda$，则： 
$
  A = dirlim_lambda A_lambda
$
从而： 
$
  X = Spec(A) = invlim_lambda Spec(A_lambda)
$
这是 Noether 概形的逆向极限，更确切地说，是 $ZZ$ 上有限型概形的逆向极限。进一步，给定有限展示的态射 $A -> B$，可以把它写成： 
$
  B cong A[t_1, dots.c, t_n]/((g_1 (arrow(t)), dots.c, g_m (arrow(t))))
$
它由有限多个生成元与关系给出。然而，每个多项式 $g_i in A[t_1, dots.c, t_n]$ 都只有有限多个系数，而每个系数都落在某个阶段对应的环 $A_lambda$ 中。于是存在某个有限阶段 $lambda_i$，使得 $g_i in A_(lambda_i) [t_1, dots.c, t_n]$。取 $lambda_1, dots.c, lambda_m$ 的一个上界 $mu$，便知对这样的 $mu$ 有 $g_1, dots.c, g_m in A_mu [t_1, dots.c, t_n]$。现在对一切 $lambda >= mu$ 取： 
$
  B_lambda = (A_lambda [t_1, dots.c, t_n])/((g_1 (arrow(t)), dots.c, g_m (arrow(t))))
$
于是立刻看出，对一切 $lambda >= mu$，$A_lambda -> B_lambda$ 都是 $A_mu -> B_mu$ 沿 $A_mu -> A_lambda$ 的基变换。此外，$A -> B$ 是 $A_lambda -> B_lambda$ 沿 $A_lambda -> A$ 的基变换。 

换言之，任何有限展示的态射 $A -> B$ 都必然来自某个有限阶段上同样有限展示的态射 $A_mu -> B_mu$。 

接下来我们考虑态射 $A -> B$ 的性质。仅作演示，我们只看一个简单的性质：$A -> B$ 满射，即 $Spec(B) -> Spec(A)$ 是闭浸入。换言之，每个 $t_i in B$ 都落在 $A -> B$ 的像里，或者说存在 $h_(i,j) in A[t_1, dots.c, t_n]$，使得 
$
  t_i = sum_(j=1)^m h_(i,j) g_j, forall 1 <= i <= n
$
然而，这有限多个多项式 ${h_(i,j)}$ 总共只有有限多个系数，它们可能全都落在某个阶段对应的环 $A_(mu')$ 中。于是必要时把 $mu$ 放大，便知对一切 $lambda >= mu$，$A_lambda -> B_lambda$ 都满射。 

上面这几段并不是在严格证明任何定理。不过，它们给出了如下直观： 

- 满足某种有限性条件（比如仿射）的概形，是 Noether 概形的逆向极限； 

- 到这种概形的态射，只要满足某种有限性条件（比如仿射且有限展示），就必然来自极限中某个有限阶段上态射的基变换； 

- 态射的某些性质（比如是闭浸入）会下降到极限中足够靠后的阶段。 

本附录余下部分给出若干定理，用最一般的方式说明上面三句话里的“某种”究竟指什么。我们不给出任何证明，因为这些证明显得过于技术化，哪怕对这份本来就相当啰嗦的讲义来说也是如此。我们只给出 Stacks Project 中的出处。 

要回答的第一个问题是概形的逼近。结果表明，正确的有限性条件正是拟紧拟分离： 
#theorem(name: <absolute-noetherian-approx>)[
  （绝对 Noether 逼近） 任意拟紧拟分离概形 $X$ 都可以写成逆向极限： 
  $
    X = invlim_i X_i
  $
  该逆向极限取在概形范畴中，所有过渡映射都是仿射的，且每个 $X_i$ 都是 $ZZ$ 上有限型的。 
]
#proof[
  见 #cite-stacks("01ZA")[Lemma 32.5.4]。 
]

#theorem(name: <relative-approx>)[
  (相对逼近) 给定概形之间的任意态射 $f: X -> S$，其中 $X$ 是拟紧拟分离的、$S$ 是拟分离的，则 $X$ 可以写成逆向极限： 
  $
    X = invlim_i X_i
  $
  该逆向极限取在概形范畴中，其中每个 $X_i$ 都是 $S$ 上有限展示的 $S$-概形，且所有过渡映射都是仿射 $S$-态射。 
]
#proof[
  见 #cite-stacks("09MV")[Lemma 32.7.2]。 
]

第二个问题是态射的逼近，这里正确的有限性条件是有限展示： 

#theorem(name: <passage-to-limit-of-morphisms>)[
  设 $S = invlim_i S_i$ 是拟紧拟分离概形的逆向极限，过渡映射都是仿射的。则： 

  + 给定任意有限展示的态射 $X -> S$，存在某个有限阶段 $i$ 与某个有限展示的态射 $X_i -> S_i$，它沿 $S -> S_i$ 的基变换恰好是 $X -> S$。 

  + 给定 $S$-概形的态射 $phi: X -> Y$。设对某个有限阶段 $i$ 与有限展示的 $S_i$-概形 $X_i, Y_i$ 有 $X = X_i times_(S_i) S, Y = Y_i times_(S_i) S$。则存在某个更靠后的阶段 $i' >= i$，以及态射 $phi_(i'): X_(i') -> Y_(i')$，它沿 $S -> S_(i')$ 的基变换是 $phi$。 

  + 给定有限阶段 $i$、有限展示的 $S_i$-概形 $X_i, Y_i$，以及两个态射 $phi_i, psi_i: X_i -> Y_i$；若它们沿 $S -> S_i$ 的基变换相等，则存在更靠后的阶段 $i' >= i$，使得 $phi_i$ 与 $psi_i$ 沿 $S_(i') -> S_i$ 的基变换相等。 
]
#proof[
  见 #cite-stacks("01ZM")[Lemma 32.10.1]。 
]

用白话说： 

- 有限展示的 $S$-概形，是把某个 $i$ 上有限展示的 $S_i$-概形作基变换得到的； 

- 有限展示的 $S$-概形之间的态射，是把某个 $i$ 上 $S_i$-概形之间的态射作基变换得到的； 

- 在极限中相等的态射，在某个有限阶段上就相等。 

对有限展示的拟凝聚层，也有类似的极限结论。 

#theorem(name: <passage-to-limit-of-sheaves>)[
  设 $S = invlim_i S_i$ 是拟紧拟分离概形的逆向极限，过渡映射都是仿射的。把过渡态射记为 $f_(i',i): S_(i') -> S_i$，投影记为 $f_i: S -> S_i$。则：
  
  + 给定任意有限展示的 $cal(O)_S$-模 $cal(F)$，存在有限阶段 $i$ 与有限展示的 $cal(O)_(S_i)$-模 $cal(F)_i$，使得 $cal(F) cong f_i^* cal(F)_i$。 
  
  + 给定有限展示的 $cal(O)_(S_i)$-模 $cal(F)_i, cal(G)_i$ 以及态射 $phi: f_i^* cal(F)_i -> f_i^* cal(G)_i$，存在更靠后的阶段 $i' >= i$ 与态射 $phi_(i'): f_(i',i)^* cal(F)_i -> f_(i',i)^* cal(G)_i$，使得 $phi = f_(i')^* phi_(i')$。 
  
  + 给定有限展示的 $cal(O)_(S_i)$-模 $cal(F)_i, cal(G)_i$ 以及态射 $phi_i, psi_i: cal(F)_i -> cal(G)_i$；若 $f_i^* phi_i = f_i^* psi_i$，则存在更靠后的阶段 $i' >= i$，使得 $f_(i',i)^* phi_i = f_(i',i)^* psi_i$。 
]
#proof[
  见 #cite-stacks("01ZR")[Lemma 32.10.2]。 
]

最后，我们研究哪些性质能从极限传到某个有限阶段。 

#theorem(name: <passage-to-limit-of-properties>)[
  设 $S = invlim_(i in I) S_i$ 是拟紧拟分离概形的逆向极限，过渡映射都是仿射的；设 $0 in I$，并设 $f_0: X_0 -> Y_0$ 是拟紧拟分离 $S_0$-概形之间的态射。对任意 $i >= 0$，记 $f_i: X_i -> Y_i$ 为 $f_0$ 沿 $S_i -> S_0$ 的基变换，记 $f: X -> Y$ 为 $f_0$ 沿 $S -> S_0$ 的基变换。 
  
  若 $f$ 具有性质 $cal(P)$，总存在某个有限阶段 $0 <= i in I$，使得 $f_i$ 也具有性质 $cal(P)$，则称性质 $cal(P)$ *从极限下降* (descends from the limit)。于是： 

  + 下列性质从极限下降： 
    1. 仿射 
    + 分离 

  + 若 $f_0$ 局部有限型，则下列性质从极限下降： 
    1. 有限 
    + 闭浸入 
    + 浸入 
    + 单态射（范畴意义上的，等价地说，对角态射是同构） 
    + 紧合 

  + 若 $f_0$ 局部有限展示，则下列性质从极限下降： 
    1. 平坦 
    + 有限且局部自由（某个次数 $d$） 
    + 光滑（某个相对维数 $d$） 
    + 平展 
    + 同构 
    + 开浸入 
    + 满射 
    + 非分歧 
]
#proof[
  见 Stacks Project 的 #cite-stacks("081C")[Section 32.8]，其中给出了除 (2e) 以外所有条目的证明；至于 (2e)，见 #cite-stacks("081F")[Lemma 32.13.1]。 

  为使内容自足，我自己来证明 (3h)、(3d) 与 (3c)。对 (3h)，注意： 
  $
    0 = Omega_(X\/Y) = Omega_(X_i\/Y_i)|_X
  $
  其中每个 $Omega_(X_i\/Y_i)$ 都是有限展示的拟凝聚 $cal(O)_(X_i)$-模层。由 @passage-to-limit-of-sheaves (3)，$Omega_(X\/Y)$ 上的恒等式 $id = 0$ 下降到某个有限阶段，故对某个 $i$ 有 $Omega_(X_i\/Y_i) = 0$。 

  (3d) 由 (3a) 与 (3h) 推出，因为平展性无非就是非分歧性加上平坦性。 

  对 (3c)，由 @equiv-defns-of-smooth (3)，在 $X$ 的每一点附近，$f$ 都分解为 $U ->^j AA^d_Y -> Y$，其中 $j$ 平展。不妨取 $U$ 为仿射开集。 

  开浸入 $U -> X$ 是有限展示的。于是由 @passage-to-limit-of-morphisms (2)，存在某个有限阶段 $i$，使得 $U -> X$ 是某个态射 $U_i -> X_i$ 的基变换，其中 $U_i$ 是某个 $S_i$-概形。把 $i$ 放大，由 (3f) 不妨设 $U_i -> X_i$ 是开浸入。 
  
  而 $j$ 是有限展示的态射。于是把 $i$ 放大，不妨设 $j$ 来自某个 $S_i$-态射 $j_i: U_i -> AA^d_(Y_i)$ 的基变换。由 (3c)，只要 $i$ 足够大，$j_i$ 就平展。现在： 
  $
    U_i ->^(j_i) AA^d_(Y_i) -> Y_i
  $
  这个复合与 $f_i|_(U_i)$ 作基变换到极限后，都等于 $f|_U$。由 @passage-to-limit-of-morphisms (3)，它们基变换到某个有限阶段后便一致。因此存在有限阶段 $i$，使得 $f_i|_(U_i)$ 是相对维数 $d$ 的光滑态射。 

  由于 $X$ 是拟紧拟分离的，可以用带平展图表的仿射开集覆盖它；这些图表只有有限多个，取相应有限阶段的上界，就把光滑性下降下来了。这就完成了 (3c) 的证明。 
]

#remark[
  使用极限论证主要有两种方式。 

  + 由 @absolute-noetherian-approx，任意拟紧拟分离概形都是有限型 $ZZ$-概形的逆向极限，过渡映射都是仿射的。据此可以把关于拟紧拟分离概形的命题归约到关于 $ZZ$ 上有限型概形的命题，特别地，归约到关于 Noether 概形的命题。 

  + $Spec(cal(O)_(X,x)) = invlim_(x in U subset X \ U #[仿射]) U$ 是仿射概形的逆向极限。据此可以把单个点处的性质铺开到开邻域上。 

    #example(name: <generic-flatness>)[
      为演示如何使用 (2)，我们说明 (2) 可以用来证明一般平坦性： 

      - 对任意态射 $f: X -> Y$，若 $Y$ 是整概形，则存在非空开集 $V subset Y$，使得 $f: f^(-1)(V) -> V$ 平坦。 

      设 $eta in Y$ 是泛点。此时 $Spec(cal(O)_(Y,eta)) = Spec(K(Y))$ 是域的谱。因此基变换 $X_eta -> eta$，即泛纤维，自动平坦。把极限论证用到这个逆向极限上： 
      $
        Spec(cal(O)_(Y,eta)) = invlim_(#[仿射开集] emptyset != V subset Y) V
      $
      便知存在非空仿射开集 $V subset Y$，使得 $f: f^(-1)(V) -> V$ 平坦。 
    ]
]
