#import "void-import.typ": *
#let topp = math.op[top]
#let LIsom = math.op[LIsom]
#let Open = math.op[Open]
/*
#date[第 3 讲，2025/10/11
  #align(left)[
    回忆一下：我们已经引入了平展态射，并研究了它们的性质。平展态射相当于概形论里的局部同胚。

    今天我们要介绍平展景与 fpqc 下降。
  ]
]*/
上一章我们定义了平展基本群 $pi_1^et (X)$。第 1 章已经给出了动机，代数拓扑也提供了类比，因此接下来的任务，就是建立一套令人满意的概形上同调理论。

在代数拓扑里，上同调理论是用层上同调定义的。拓扑空间 $X$ 上的层，就是一个满足某些“层公理”的函子 $Open_X^opp -> cAb$，即从 $X$ 的开集到交换群的反变函子。层上同调则是把整体截面函子 $Gamma(X, -): cAb(X) -> cAb$ 右导出得到的；而我们熟悉的带系数的奇异上同调 $H^p (X, Lambda)$，也就可以定义为常值层 $underline(Lambda)$ 的层上同调。

然而这并不能为概形提供一套令人满意的上同调理论。在一个典型的概形上——比如不可约概形——常值层是松弛的，它的所有高阶上同调都消没。

事实证明，毛病就出在 Zariski 拓扑太粗。解决这个问题的正确办法，是把层的概念推广出去：在 $Open_X^opp -> cAb$ 中，把开集构成的范畴 $Open_X$ 换成 $X$ 上平展态射构成的范畴 $Et_X$。直观地说，每个开浸入都是平展的，所以平展邻域更细，能捕捉到关于这个概形的更多信息。

于是，接下来我们要把 $Open_X$ 与 $Et_X$ 的共同之处提炼成一般的概念，建立景 (site) 与层的抽象理论，定义平展景与平展层，再把基本的层运算引入平展层。

== 景与平展景

在开始讲平展景之前，我们先定义抽象景的一般概念。

#definition(name: <defn-site>)[
  所谓*景* $cal(T)$，指的是一个范畴 $cal(C)$，外加如下数据：对每个对象 $X in cal(C)$ 指定一族态射 ${X_i -> X}$。这些族称为 $X$ 在 $cal(T)$ 中的*覆盖*，且须满足以下公理：

  + 单个同构 ${V ->^tilde U}$ 是 $U$ 在 $cal(T)$ 中的一个覆盖；

  + 对 $U$ 在 $cal(T)$ 中的任意覆盖 ${U_i -> U}_(i in I)$ 与 $cal(C)$ 中的任意态射 $V -> U$，纤维积 $U_i times_U V$ 在 $cal(C)$ 中存在，且 ${U_i times_U V -> V}_(i in I)$ 是 $V$ 在 $cal(T)$ 中的一个覆盖；

  + 若：
    - ${U_i -> U}_(i in I)$ 是 $U$ 在 $cal(T)$ 中的一个覆盖；

    - 对每个 $i$，${U_(i,j) -> U_i}_(j in J_i)$ 是 $U_i$ 在 $cal(T)$ 中的一个覆盖；
    则 ${U_(i,j) -> U}_(i in I, j in J_i)$ 是 $U$ 在 $cal(T)$ 中的一个覆盖。
  
  于是我们可以用同样的方式定义 $cPSh(cal(C)), cPAb(cal(C))$ 与 $cSh(cal(C)), cAb(cal(C))$。
  
  例如，对拓扑空间 $X$，景 $X_topp = (Open(X), "开覆盖")$ 给出的正是 $X$ 上的层的通常概念。
]

#definition(name: <defn-presheaves-and-sheaves-on-sites>)[
  设 $cal(T)$ 是一个底范畴为 $cal(C)$ 的景。我们定义：

  - *$cal(T)$ 上的集合预层 (presheaf) 与交换群预层*，定义为函子 $cal(C)^opp -> cSet$（相应地，$cal(C)^opp -> cAb$）。
  
    预层之间的态射，定义为它们作为反变函子的自然变换。$cal(T)$ 上的集合预层与交换群预层构成的范畴，分别记作 $cPSh(cal(T))$ 与 $cPAb(cal(T))$。

  - *$cal(T)$ 上的集合层/交换群层*，指的是 $cal(T)$ 上一个取值于集合（相应地，交换群）的预层 $cal(F)$，它满足下面的层公理：

    - 对任意 $X in cal(C)$ 与任意覆盖 ${U_i -> X}_(i in I)$，都有集合的等化子：#h(1fr)
      $
        cal(F)(X) ->^(u |-> (u|_(U_i))_i) product_(i in I) cal(F)(U_i) arrows.rr^((u_i)_i |-> (u_i|_(U_i times_X U_j))_(i,j))_((u_i)_i |-> (u_j|_(U_i times_X U_j))_(i,j)) product_(i,j in I) cal(F)(U_i times_X U_j) 
      $
      换言之，若一族截面 $(u_i)_(i in I) in product_(i in I) cal(F)(U_i)$ 在所有 $U_i times_X U_j$ 上都相容，则它们粘成唯一的截面 $u in cal(F)(U)$。

    集合层/交换群层之间的态射，就是它们作为预层之间的态射。$cal(T)$ 上的集合层与交换群层构成的范畴，分别记作 $cSh(cal(T))$ 与 $cAb(cal(T))$。
]

#example[
  景的典型例子是*拓扑景* (topological site) $X_topp$。设 $Open_X$ 是以 $X$ 的开集为对象、以开集包含为态射的范畴。则 $X_topp = (Open_X, #[开覆盖])$ 是一个景。（纤维积就是开集的交。开覆盖对交稳定，并且是传递的。）

  此时，$X$ 上的（交换群）预层 $cal(F)$ 不过是函子 $Open_X^opp -> cAb$，其中 $Open_X$ 如前。层条件说的是：给定 $U subset X$ 与开覆盖 ${U_i}$，都有正合列：
  $
    0 -> cal(F) (U) -> product_i cal(F)(U_i) -> product_(i,j) cal(F)(U_i ∩ U_j)
  $
  其中态射就是你熟悉的那两个。

  $X_#[top]$ 还有一个小变式：取 $LIsom_X$ 为局部同胚 $f: Y -> X$ 构成的范畴，若 $X = union.big_i h_i (Y_i)$，则称态射族 ${h_i: Y_i -> X}$ 为覆盖。此时纤维积在 $LIsom_X$ 中存在，且 $Open_X$ 全忠实地嵌入 $LIsom_X$。我们把这个景记作 $X_LIsom$。
  
  $LIsom_X$ 上的预层，是反变函子 $cal(G): LIsom_X^opp -> cSet$。若对任意覆盖 ${h_i: Y_i -> Y}$，
  $
    cal(G) (Y) -> product_(i) cal(G) (Y_i) arrows.rr product_(i,j) cal(G) (Y_i times_Y Y_j)
  $
  都是等化子，则称 $cal(G)$ 是层。

  #fact[
    把开覆盖换成用局部同胚作覆盖，这个推广其实并没有引入任何新东西。严格地说，存在范畴之间的自然等价：
    $
      cSh(X_topp) cong cSh(X_LIsom), cAb(X_topp) cong cAb(X_LIsom)
    $
  ]

  因此 $X_LIsom$ 实际上只是 $X_topp$ 的一个新视角。它有一个新特点：可以沿 $LIsom_X$ 中的覆盖把层粘起来。设 ${g_i : X_i -> X}$ 是 $id: X -> X$ 在 $LIsom_X$ 中的一个覆盖。给定 $cal(F)_i in cSh(LIsom_(X_i))$，以及在 $LIsom_(X_i times_X X_j)$ 上的层同构 $eta_(i,j) : p_1^* cal(F)_i -> p_2^* cal(F)_j$，使得余圈条件
  $
    p_(13)^* eta_(i,k) = p_(23)^* eta_(j,k) compose p_(12)^* eta_(i,j)
  $
  在 $LIsom_(X_i times_X X_j times_X X_k)$ 上成立。于是存在唯一的 $cal(F) in cSh(LIsom_X)$，以及一个与 $eta_(i,j)$ 相容的同构 $cal(F)|_(X_i) cong cal(F)_i$。换言之，存在范畴等价
  $
    cSh(X_topp) cong cSh(X_LIsom) cong "DD"(g_i) = {(cal(F)_i, eta_(i,j)) "使得" dots.c}
  $
  其中右端是下降数据构成的范畴。
]

/*
#example[
  动机是这样的：在拓扑空间 $X$ 上，我们可以考虑层上同调 $H^bullet (X, cal(F)), cal(F) in cAb(X)$。

  此时，$X$ 上的预层 $cal(F)$ 不过是函子 $Open_X^opp -> cAb$，其中 $Open_X$ 是以 $X$ 的开集为对象、以开集包含为态射的范畴。层条件说的是：给定 $U subset X$ 与开覆盖 ${U_i}$，都有正合列：
  $
    0 -> cal(F) (U) -> product_i cal(F)(U_i) -> product_(i,j) cal(F)(U_i ∩ U_j) -> 0
  $
  其中态射是#furi[Čech 复形的前两个映射][你熟悉的那两个]。

  这个构造的一个变形，是取 $LIsom_X$ 为局部同胚 $f: Y -> X$ 构成的范畴，并称一族态射 ${h_i: Y_i -> X}$ 是覆盖，若 $X = union.big_i h_i (Y_i)$。此时纤维积在 $LIsom_X$ 中存在，且 $Open_X$ 全忠实地嵌入 $LIsom_X$。$LIsom_X$ 上的预层是反变函子 $cal(G): LIsom_X^opp -> cSet$。若对任意覆盖 ${h_i: Y_i -> Y}$，
  $
    cal(G) (Y) -> product_(i) cal(G) (Y_i) arrows.rr product_(i,j) cal(G) (Y_i times_Y Y_j)
  $

  #exercise[
    我们有范畴等价：
    $
      cSh(Open_X) & tilde.eq cSh(LIsom_X) \
      cal(F) &|-> ((g: Y -> X) |-> (g^(-1) cal(F))(Y)) \
      cal(G)|_(Open_X^opp) &#scale(x: -100%)[$|->$] cal(G)
    $
  ]
  
  所以这个新表述其实只是一个新视角。它带来一个新特点：我们可以沿 $LIsom_X$ 中的覆盖把层粘起来。设 ${g_i : X_i -> X}$ 是 $id: X -> X$ 在 $LIsom_X$ 中的一个覆盖。给定 $cal(F)_i in cSh(LIsom_(X_i))$，以及在 $LIsom_(X_i times_X X_j)$ 上的层同构 $eta_(i,j) : p_1^* cal(F)_i -> p_2^* cal(F)_j$，使得余圈条件：
  $
    p_(13)^* eta_(i,k) = p_(23)^* eta_(j,k) compose p_(12)^* eta_(i,j)
  $
  在 $LIsom_(X_i times_X X_j times_X X_k)$ 上成立。于是存在唯一的 $cal(F) in cSh(LIsom_X)$，以及与 $eta_(i,j)$ 相容的同构 $cal(F)|_(X_i) cong cal(F)_i$。

  #exercise[
    $
      cSh(LIsom_X) tilde.eq "DD"(g_i) = {(cal(F)_i, eta_(i,j)) "使得" dots.c}
    $
    其中右端是下降数据构成的范畴。
  ]

  #remark[
    若某个 $g_i: X_i -> X$ 有截面 $s_i: X -> X$，这个构造就非常容易：此时 $X$ 几乎可以看成 $X_i$ 的一个开集，于是可以取 $cal(F) = s^(-1) cal(F)_i$。
  ]

  这套设置是景的一个例子。更正式地说，一个景就是某个范畴连同上的一种覆盖概念，并满足若干公理。
]*/

景的一般概念、以及一般景上的层 (toposes)，对某些数学家来说相当重要；但这门课只是平展上同调的入门，我们用不到这个观点。在本书剩下的部分里，“景”这个字眼除了出现在“平展景”这个说法里，就很少再出现了。下面我们就要引入平展景了，前两页里介绍的那些抽象概念，你大可以忘掉大半。

// 现在可以定义 $Et_X$ 了，即平展景范畴：
#definition(name: <defn-etale-site>)[
  概形 $X$ 上的*平展景* $X_et$，是由以下数据定义的范畴：

  - $X_et$ 的底范畴是范畴 $Et_X$，它定义为 $cSch_X$ 的满子范畴，由平展态射 $f: Y -> X$ 组成。
  
    这个范畴里的态射，先验地可以是任意与 $Y -> X$、$Z -> X$ 交换的态射 $h: Y -> Z$；但由平展态射的性质，它们必然也是平展的。

  - 给定 $(h: Y -> X) in Et_X$，若 $Et_X$ 中一族态射 ${h_i: Y_i -> Y}_(i in I)$ 满足 $Y = union.big_i h_i (Y_i)$，则称这族态射为 $Y$ 的一个*覆盖*。这个条件称为*联合满射*。

  范畴 $Et_X$ 的纤维积由基变换给出；平展态射的复合仍是平展的；同构都是满射；联合满射性对基变换稳定，并且是传递的。因此，
  $
    X_et = (Et_X, #[联合满射的平展态射族])
  $ 
  是一个景。

  注意记号：我们用 $X_et$ 表示这个景，用 $Et_X$ 表示它的底范畴。

  $X$ 上的*平展预层/层* (étale presheaf/sheaf)，就是 $X_et$ 上取值于集合/交换群的预层/层，与我们为一般景所定义的一样。这些范畴按一般情形记作 $cPSh(X_et)$、$cSh(X_et)$、$cPAb(X_et)$、$cAb(X_et)$。
]
