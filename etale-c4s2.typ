#import "void-import.typ": *
== 平展层的例子

/*
设 $X$ 是概形，$Et_X$ 是平展 $X$-概形构成的范畴。回忆 $X_et = (Et_X, "平展覆盖")$ 是 $X$ 的平展景。这里，若 ${f_i: Z_i -> Z}$ 联合满射，即 $Z = union.big_i f_i (Z_i)$，则称它为平展覆盖。

回忆我们在 $X_et$ 上把预层 $cPSh(X_et)$ 定义为函子 $cal(F): Et_X^opp -> cSet$，把层 $cSh(X_et)$ 定义为这样的预层：对任意平展覆盖 ${f_i: Z_i -> Z}$，
$
  cal(F) -> product_i cal(F)(Z_i) arrows.rr product_(i,j) cal(F)(Z_i times_Z Z_j)
$
都正合。把 $cSet$ 换成 $cAb$，就得到 $cPAb(X_et)$ 与 $cAb(X_et)$。
*/
一如既往，引入一个对象之后，我们总要研究它的基本性质。对平展层而言，可以借助与拓扑层的类比，预期需要哪些构造。具体来说，我们需要：
- 平展层的例子；
- 层化 (sheafification)；
- $cAb(X_et)$ 是 Abel 范畴（也就是要定义核、余核与像）；
- $cAb(X_et)$ 有足够多的内射对象；
- 对概形间的态射 $f: X -> Y$，有伴随对 $f_*: cAb(X_et) arrows.rl cAb(Y_et): f^(-1)$。

本节及接下来几节将讨论这些话题。我们安排各节的方式，对应着获取 $X$ 上平展层的几种方法：
- 直接作为基本例子之一构造；
- 来自 $cAb(X_et)$ 的 Abel 范畴结构，即取作 $X$ 上平展层之间态射的核、余核或像；
- 来自函子性：把 $f_*, f^(-1)$（以及很久以后才会引入的 $f_!$）这样的函子或它们的导出版本，作用于另一个概形上的平展层。

#lemma[
  (集合的九引理) 假设有集合的图表：
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
  其中每个平行四边形都交换，即：
  $
    alpha_2 compose f_1 = alpha_1 compose f_2 \
    alpha_3 compose g_(1,i) = g_(2,i) compose alpha_2, forall i in {1,2} \
    beta_(2,j) compose f_2 = f_3 compose beta_(1,j), forall j in {1,2} \
    beta_(3,j) compose g_(2,i) = g_(3,i) compose beta_(2,j), forall i,j in {1, 2}
  $
  若三列与最下面两行都是等化子，则最上面一行也是。此外，在下面这组更弱的假设下，最上面一行仍是等化子：
  - $alpha_(1,2,3)$ 与 $f_(2,3)$ 都是单射；
  - 中间一行是等化子；
  - $beta_(1,1),beta_(1,2)$ 的等化子穿过 $alpha_1 (A_1)$ 分解（即包含于其中）。
  在这组更弱的假设下，实际上可以把 $g_(3,i)$ 与 $beta_(3,j)$ 从图表中去掉。
]
#proof[
  这不过是无聊的追图，请跳过。

  由于 $alpha_1, f_2$ 都是单射，$alpha_2 compose f_1 = alpha_1 compose f_2$ 也是单射，故 $f_1$ 是单射。此外，对 $i in {1, 2}$，
  $
    alpha_3 compose g_(1,i) compose f_1 = g_(2,i) compose f_2 compose alpha_1
  $
  由于 $g_(2,1) compose f_2 = g_(2,2) compose f_2$，有 $alpha_3 compose g_(1,1) compose f_1 = alpha_3 compose g_(1,2) compose f_1$。又因 $alpha_3$ 是单射，可以左消去它，得到 $g_(1,1) compose f_1 = g_(1,2) compose f_1$。

  要证最上面一行是等化子，剩下只需证明：若 $g_(1,1)(b_1) = g_(1,2)(b_1)$，则 $b_1 in f_1 (A_1)$。对等式两边作用 $alpha_3$，得到 $g_(2,1)(alpha_2 (b_1)) = g_(2,2) (alpha_2 (b_1))$。由于中间一行是等化子，存在 $a_2 in A_2$ 使得 $alpha_2 (b_1) = f_2 (a_2)$。对等式两边作用 $beta_(2,j)$，得到 $beta_(2,1) (f_2 (a_2)) = beta_(2,1) (alpha_2 (b_1)) = beta_(2,2) (alpha_2 (b_1)) = beta_(2,2) (f_2 (a_2))$。换言之，$f_3 (beta_(1,1) (a_2)) = f_3 (beta_(1,2) (a_2))$。由于 $f_3$ 是单射，$beta_(1,1) (a_2) = beta_(1,2) (a_2)$。由于左列是等化子，存在 $a_1 in A_1$ 使得 $a_2 = alpha_1 (a_1)$。现在 $alpha_2 (b_1) = f_2 (alpha_1 (a_1)) = alpha_2 (f_1 (a_1))$，而 $alpha_2$ 是单射，故 $b_1 = f_1 (a_1)$。

  仔细检查证明可以发现，用到的条件只有：
  - $alpha_(1,2,3)$ 与 $f_(2,3)$ 是单射；
  - 中间一行是等化子；
  - 左列满足：若 $beta_(1,1)(a_2) = beta_(1,2)(a_2)$，则 $a_2 in alpha_1 (A_1)$。也就是说，$beta_(1,1),beta_(1,2)$ 的等化子穿过 $alpha_1 (A_1)$ 分解（即包含于其中）。
]

#lemma(name: <etale-cover-equiv-conds>)[
  设 $cal(F) in cPSh(X_et)$ 或 $cPAb(X_et)$，则以下条件等价：

  + $cal(F) in cSh(X_et)$（相应地 $cAb(X_et)$），即 $cal(F)$ 对 $X_et$ 中每个平展覆盖都满足层条件；

  + $cal(F)$ 对以下覆盖满足层条件：
    + 每个 Zariski 覆盖；
    + $X_et$ 中每个由单个映射组成的平展覆盖。

  + $cal(F)$ 对以下覆盖满足层条件：
    + 每个 Zariski 覆盖；
    + $X_et$ 中形如 ${Z_i -> Z}_(i in I)$ 的每个平展覆盖，其中指标集 $I$ 有限，$Z$ 与每个 $Z_i$ 都拟紧。

  + $cal(F)$ 对以下覆盖满足层条件：
    + 每个 Zariski 覆盖；
    + $X_et$ 中每个由单个映射 $Z' -> Z$ 组成的平展覆盖，其中 $Z', Z$ 都仿射。

  // + $cal(F)$ 对以下覆盖满足层条件：
  //   + 每个 Zariski 覆盖；
  //   + $X_et$ 中每个由单个映射 $Z' -> Z$ 组成的平展覆盖，其中 $Z', Z$ 都仿射。
]
#proof[
  交换群层不过是满足集合层条件的交换群预层，故只需考虑集合的情形 $cal(F) in cPSh(X_et)$。/*注意在 (a) 之下，(b) 与 (b') 等价：可以把有限族 ${f_i: Z_i -> Z}$ 换成 $f': Z' = union.sq.big_(i in I) Z_i -> Z$。若每个 $Z_i$ 都拟紧，则 $Z'$ 也拟紧。因此可以假定条件 (a)(b) 成立。*/

  假定每个 Zariski 覆盖的层条件都成立，则用覆盖 ${U_i -> union.sq.big_(i in I) U_i}_(i in I)$ 可以验证存在典范同构：
  $
    cal(F)(union.sq.big_(i in I) U_i) cong product_(i in I) cal(F)(U_i)
  $
  于是立刻看出，一般平展覆盖 ${Z_i -> Z}_(i in I)$ 的层条件，等价于由单个映射组成的平展覆盖 $union.sq.big_(i in I) Z_i -> Z$ 的层条件。由此立即得到 (1) $<==>$(2) $==>$(3) $==>$(4)。
  
  下面重点证明 (4) $==>$(2)。任取平展覆盖 $g: W' -> W$，用仿射开集 $union.big_p U_p$ 覆盖 $W$，得到图表：
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
  其中平行四边形都交换。各列分别是 $W$、$W'$ 与 $W' times_W W'$ 上 Zariski 覆盖的层条件所给出的等化子。

  我们再加一个辅助条件：
  #[
    #set enum(numbering: _ => "(c)")

    + 对任意 $U in Et_X$，若它是仿射概形，则它的所有由单个映射组成的平展覆盖都满足层条件。
  ]

  在此假设下，中间一行是仿射概形 $U_p$ 上某个平展覆盖的层条件，因而是等化子。于是：

  - 在左上角的方块中，左边与下边的箭头都是单射，故上边的箭头必是单射。
  
  - 由于 $W$ 是任意的，由前一点可知：对每个 $Z in Et_X$ 与 $Et_X$ 中每个平展覆盖 $Z' -> Z$，映射 $cal(F)(Z) -> cal(F)(Z')$ 都是单射。特别地，它对每个 $(U_p ∩ U_q) times_W W' -> U_p ∩ U_q$ 成立。换言之，最后一行的第一个箭头是单射。

    现在所有列与第二行都是等化子，且第一行与第三行的第一个箭头都是单射，故可对集合套用九引理，于是第一行的第一个箭头是等化子。

  于是，一般层条件归结为 (c)。我们还需证明：对 $Et_X$ 中任意满射平展映射 $U' -> U$（其中 $U$ 仿射），层条件都成立。

  对平展覆盖 ${Z_i -> Z}_(i in I)$，若下述映射
  $
    cal(F)(Z) -> product_(i in I) cal(F)(Z_i)
  $
  是单射，则称 $cal(F)$ 关于该覆盖是分离预层 (separated presheaf)。我们再引入一个条件：
  #[
    #set enum(numbering: _ => "(cs)")
    + $cal(F)$ 关于仿射 $U in Et_X$ 的所有平展覆盖都是分离预层。
  ]
  注意借助不交并，可以把“平展覆盖由单个映射组成”这一条平凡地并入 (cs)，而不削弱它。由上面九引理图表左上角的方块可知 (cs) $==>$(s)，其中：
  #[
    #set enum(numbering: _ => "(s)")
    + $cal(F)$ 关于所有平展覆盖都是分离预层。
  ]

  接下来，我们由下面这个更弱的条件 (d) 推出 (c)：
  #[
    #set enum(numbering: _ => "(d)")
    + 对 $cal(F)$，层条件对所有平展覆盖 ${U_i -> U}_(i in I)$ 成立，只要 $U$ 与每个 $U_i$ 都仿射；也就是说，层条件对所有平展 $V -> U$（其中 $V$ 是仿射概形的不交并）都成立。
  ]
  
  设 $U$ 仿射，$W -> U$ 是任意平展覆盖。用仿射开集 ${V_i}_(i in I)$ 覆盖 $W$，并令 $V = union.sq.big_(i in I) V_i$，于是 $Et_X$ 中有 $V ->> W ->> U$。考虑下面这个图表，其中平行四边形都交换：
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
  其中底行由 (d) 知是等化子。于是：

  - 在左边的方块中，$f_2 = beta compose f_1$ 是单射，故 $f_1$ 是单射。由于 $W$ 是任意的，这证明了 (cs)。

  - 由 (cs) $==>$(s) 得到 (s)，于是 $f_1, beta, gamma$ 都是单射。经追图可知第一行是等化子，从而得到 (c)。
  
    （若愿意细读，这里就是具体的追图。首先，对 $i = 1,2$，$gamma compose g_(1,i) compose f_1 = g_(2,i) compose beta compose f_1 = g_(2,i) compose f_2$ 都成立。由于 $gamma$ 是单射，可以左消去它，得到 $g_(1,1) compose f_1 = g_(1,2) compose f_1$。若 $b in cal(F)(W)$ 满足 $g_(1,1)(b) = g_(1,2)(b)$，则作用 $gamma$ 并利用右边交换的平行四边形，得到 $g_(2,1)(beta(b)) = g_(2,2)(beta(b))$。由于底行是等化子，存在 $a in cal(F)(U)$ 使得 $f_2 (a) = beta(b)$，即 $beta(b) = beta(f_1(a))$。由于 $beta$ 是单射，$b = f_1 (a)$。）

  总之，我们已证 (d) $==>$(c)，故只需再证 (d)。考虑平展覆盖 $U' = union.sq.big_(i in I) U_i -> U$，其中每个 $U_i$ 与 $U$ 都仿射。由于 $U$ 拟紧，存在有限子族 $J subset I$，使得 $U'_1 = union.sq.big_(i in J) U_i -> U$ 满射。换言之，$U'_1$ 仿射，且 $U'_1 -> U$ 满射平展。下面考虑图表：

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
  其中平行四边形都交换。现在：
  - 每一列都是层条件序列的直积；这些序列对应平展覆盖 $W times_U U'_1 -> W$，其中 $W = U, U_i$ 或 $U_i times_U U_j$。由 (4b)，每一列都是等化子。

  - $U'_1 times_U U' -> U'_1$ 有截面 $(id, subset): U'_1 -> U'_1 times_U U'$。类似地，$U'_1 times_U U'_1 times_U U' -> U'_1 times_U U'_1$ 也有截面 $(id_(U'_1 times_U U'_1), Delta)$。由下述引理，最下面两行是等化子：
    #lemma[
      对任意 $cal(F) in cPSh(X_et)$，若 $Et_X$ 中的态射 $f: Z -> Y$ 有截面 $s: Y -> Z$，则层条件对 $f: Z -> Y$ 成立。
    ]
    #proof[
      我们要证明：
      $
        cal(F)(Y) ->^(cal(F)(f)) cal(F)(Z) arrows.rr^(cal(F)(p_1))_(cal(F)(p_2)) cal(F)(Z times_Y Z)
      $
      是等化子。首先注意，由于 $f compose s = id$，有 $cal(F)(s) compose cal(F)(f) = id$，故 $cal(F)(f)$ 是单射。此外，$f compose p_1 = f compose p_2$ 自动成立。剩下要证：任意满足 $cal(F)(p_1)(x) = cal(F)(p_2)(x)$ 的 $x in cal(F)(Z)$ 都在 $cal(F)(f)$ 的像中。定义映射 $phi = (id, s compose f): Z -> Z times_Y Z$（这里用了 $f compose s compose f = f$）。现在：
      $
        p_1 compose phi = id_Z, p_2 compose phi = s compose f
      $
      于是把 $cal(F)(phi)$ 作用于 $cal(F)(p_1)(x) = cal(F)(p_2)(x)$，得到：
      $
        x = cal(F)(f)(cal(F)(s)(x))
      $
    ]
  由九引理，第一行是等化子，(c) 得证。

  /*
  我们先证明 (a)(b) 蕴含下面的条件 (b')：

  #[
    #set enum(numbering: _ => "(b')")
    + 对 $Et_X$ 中任意满射平展 $V -> W$（$V, W$ 拟紧）以及任意平展 $W' -> W$（$W'$ 不必拟紧），层条件对 $cal(F)$ 与 $V' = W' times_W V -> U'$ 成立。
  ]

  事实上，在 (b') 的设定下，可以用任意多个仿射开集 ${U'_i}_(i in I)$ 覆盖 $U'$。由 (b)，层条件对 $cal(F)$ 与每个 $U'_i times_U V -> U'_i$ 成立。//取 $U'' = union.sq.big_(i in I) U'_i$，则层条件对 $cal(F)$ 与 $V'' = U'' times_U V -> U''$ 必定成立。

  // 注意 $U'' -> U'$ 也是 $Et_X$ 中的满射平展映射，给出平展覆盖的加细 $U'' -> U' -> U$。考虑图表：
  考虑图表：
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


  // 思路大概是：每个 $U_p$ 都拟紧，所以或许可以把有限情形套用到最下面两行，得到某种正合性，再仿照九引理的论证。要让这套想法成立，需要做大量化归。
]

#proposition(name: <examples-of-etale-sheaves>)[
  + 对任意 $X$-概形 $Y$，#h(1fr)
    $
      h_Y : Et_X^opp -> cSet, Z |-> Hom_X (Z, Y)
    $
    是平展集合层。若进一步假设 $Y$ 是 $X$ 上的交换群概形，则 $h_Y$ 是平展交换群层。

  + 对任意 $cal(M) in QCoh(X)$，
    $
      cal(M)_et: Et_X^opp -> cAb, (f: Z -> X) |-> Gamma(Z, f^* cal(M))
    $
    是平展交换群层。
]
#proof[
  两种情形下，层条件对 Zariski 覆盖都成立。因此只需验证 @etale-cover-equiv-conds 的 (4b)。设 $Z' = Spec(A') ->> Z = Spec(A)$ 是仿射 $X$-概形的平展覆盖。
  // $
  //   cal(F)(Z') = product_i cal(F)(Z_i), cal(F)(Z' times_Z Z') = product_(i,j) cal(F)(Z_i times_Z Z_j)
  // $

  // 第 3 讲中我们证明过：
  // + 对 fpqc 态射 $f: Z' -> Z$，
  //   $
  //     Hom(Z, Y) -> Hom(Z', Y) arrows.rr Hom(Z'', Y)
  //   $
  //   正合。

  // + 拟凝聚层满足 fpqc 下降。

  (1) 我们需要等化子：
  $
    Hom_X (Z, Y) -> Hom_X (Z', Y) arrows.rr Hom_X (Z' times_Z Z', Y)
  $
  这正是 @fpqc-descent-of-morphisms，即态射的 fpqc 下降。

  (2) 设 $f: Z -> X$ 是 $Et_X$ 的对象，$cal(M) in QCoh(X)$。我们需要左正合列：
  $
    0 -> Gamma(Z, f^* cal(M)) -> Gamma(Z', f'^* cal(M)) -> Gamma(Z'', f''^* cal(M))
  $
  即左正合列：
  $
    0 -> Hom(cal(O)_Z, f^* cal(M)) -> Hom(cal(O)_(Z'), f'^* cal(M)) -> Hom(cal(O)_(Z''), f''^* cal(M))
  $
  然而，这恰好可由拟凝聚层 fpqc 下降的全忠实性得到，即 @fpqc-descent-of-sheaves。
]

#example[
  平展层有如下常见例子：

  - 层 $GG_a = cal(O)_(X,et): Et_X^opp -> cAb, Z |-> cal(O)_Z (Z)$：它把 $X$ 上每个平展概形送到其整体函数。

  - 乘法群层 $GG_m$。它是与交换群概形 $GG_(m,X) = X otimes_ZZ Spec(ZZ[x, y]\/(x y - 1))$ 相伴的平展层：
    $
      GG_m: Et_X^opp -> cAb, Z |-> Hom_X (Z, GG_(m,X)) = Hom(Z, GG_(m,ZZ)) = cal(O)_Z (Z)^times
    $

  - 层 $mu_n$，即 $n$ 次单位根层。它是与交换群概形 $mu_(n,X) = X otimes_ZZ Spec(ZZ[x]\/(x^n-1))$ 相伴的平展层：
    $
      mu_n: Et_X^opp -> cAb, Z |-> Hom_X (Z, mu_(n,X)) = Hom(Z, mu_(n,ZZ)) = {omega in cal(O)_Z (Z) : omega^n = 1}
    $
]
