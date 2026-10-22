// audit-exception: 作者 R3 意见：把 “det(…) in B” 改写为“这个行列式（作为 B 的元素）”，公式文字说明随作者要求调整，数学内容未变。
#import "void-import.typ": *

== 非分歧、平展与光滑态射

#notation(name: <kahler-differentials>)[
  设 $f: X -> Y$ 是概形之间的局部有限展示态射。则存在 Kähler 微分层 $Omega_(X\/Y)$，它是有限生成拟凝聚 $cal(O)_X$-模。
]

#example[
  局部地，设 $X = Spec(B) -> Y = Spec(A)$，其中 $B = A[x_1,dots.c,x_n]\/I$。则： 
  $
    Omega_(X\/Y) = tilde(Omega_(B\/A)), Omega_(B\/A) = (oplus.big_(i=1)^n B d x_i)/(gen(d f: f in I))
  $
  #example[
    若 $B = A[x]\/(f(x))$，则： 
    $
      Omega_(B\/A) cong A[x]\/(f(x), f'(x))
    $
    #example(name: <rel-differential-of-fin-sep-ext>)[
      若 $A = K$ 是域，且 $B = K(alpha) = K[x]\/(f(x))$ 是有限单扩张，则： 
      $
        Omega_(B\/A) = 0 <==> (f(x), f'(x)) = (1) <==> K(alpha)\/K #[有限可分]
      $
      特别地，由本原元定理，每个有限可分域扩张都是单扩张。因此只要 $L\/K$ 是有限可分扩张，就有 $Omega_(L\/K) = 0$。 
    ]
  ]
]

#proposition(name: <equiv-defns-of-unramified>)[
  设 $f: X -> Y$ 局部有限展示，$y = f(x)$，则下列条件等价： 
  + $cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x)$ 是 $k(y)$ 的有限可分扩张。（特别地，$frak(m)_x = frak(m)_y cal(O)_(X,x)$。）

  + $(Omega_(X\/Y))_x = 0$。

  + 对角态射 $Delta_(X\/Y): X -> X times_Y X$ 在 $X$ 的某个开邻域上是开浸入。 
]
#proof[
  这个问题本质上对底与源都是局部的，故不妨设 $X = Spec(B), Y = Spec(A)$ 连通，且 $B$ 是有限生成 $A$-代数。设 $x$ 对应 $frak(q) subset B$，$y$ 对应 $frak(p) subset A$。

  (2) $<==>$(3)： 
  #proof[
    首先注意，性质 (2) 与 (3) 都对 $x$ 局部。(3) 按定义对 $x$ 局部；至于 (2)，由于 $X -> Y$ 局部有限型，$Omega_(X\/Y)$ 是 $X$ 上的凝聚层，其支集是闭集，故 (2) 对 $x$ 也局部。因此可以把条件 (2)(3) 换成： 
    #[
      #set enum(numbering: "(1')")
      2. $Omega_(B\/A) = 0$； 
      3. $Delta_(X\/Y): X -> X times_Y X$ 是开浸入。 
    ]
    设 $I = ker(mu\: B otimes_A B -> B)$。由于作为 $B$-模有 $Omega_(B\/A) = I\/I^2$，故 (2') $<==>$ $I = I^2$；另一方面，仿射概形之间的态射 $Delta$ 自动是闭浸入，故 (3') $<==>$ $Delta_(X\/Y)$ 是到 $X times_Y X$ 的某些连通分支中的开浸入 $<==>$ $I = ker(mu)$ 由单个幂等元生成。于是只需证明 $I = I^2 <==> I = (e)$，其中 $e = e^2$。其中一个方向是显然的。 
    
    另一个方向：由于 $B\/A$ 有限型，$I$ 是有限生成理想。由 Nakayama 引理，存在 $e in I$ 使得 $(1-e)I = 0$。于是 $(1-e)e = 0$，故 $e=e^2$ 是幂等元，而 $I = e I$ 由 $e$ 生成。证毕。  
    #suppress-qed
  ]
  (1) $<==>$(2)： 
  #proof[
    注意，微分层在基变换下保持不变：
    $
      Omega_(X\/Y) cong i_(X_y)^* (Omega_(X_y\/k(y)))
    $
    于是：
    $
      (Omega_(X\/Y))_x otimes_(cal(O)_(X,x)) cal(O)_(X_y,x) cong (Omega_(X_y\/k(y)))_x
    $
    由于 $X$ 与 $X_y$ 在 $x$ 处的剩余域同为 $k(x)$，用 $k(x)$ 与上式两端作张量积可得：
    $
      (Omega_(X\/Y))_x otimes_(cal(O)_(X,x)) k(x) cong (Omega_(X_y\/k(y)))_x otimes_(cal(O)_(X_y,x)) k(x)
    $
    因此，
    $
      (Omega_(X\/Y))_x = 0 & <==> (Omega_(X\/Y))_x otimes_(cal(O)_(X,x)) k(x) = 0 "由 Nakayama" \
                          & <==> (Omega_(X_y\/k(y)))_x otimes_(cal(O)_(X_y,x)) k(x) = 0 \
                          & <==> (Omega_(X_y\/k(y)))_x = 0
    $
    另一方面，条件 (1) 在取纤维时同样保持不变：事实上按构造 $cal(O)_(X_y,x) = cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x)$，而一个域的极大理想是 $0$。于是取纤维后，只需证明：若 $f: X = Spec(A) -> Y = Spec(k)$ 有限型，$x in X$，则下列条件等价：

    + $cal(O)_(X,x)$ 是域，且是 $k$ 的有限可分扩张；

    + $(Omega_(X\/Y))_x = 0$。
    也就是说，这正是把 $Y$ 假定为某个域的谱时的原命题。
    
    设 $x$ 对应素理想 $frak(q) subset A$。现在： 
    $
      (Omega_(X\/k))_x = Omega_(A\/k) otimes_A A_(frak(q)) = Omega_(A_(frak(q))\/k)
    $
    因此只需证明：$Omega_(A_(frak(q))\/k) = 0$ 当且仅当 $A_(frak(q))$ 是域，且是 $k$ 的有限可分域扩张。($<==$) 方向由 @rel-differential-of-fin-sep-ext 立得，故只证 ($==>$)。$Omega_(A\/k)$ 是有限 $A$-模，故茎 $Omega_(A\/k) otimes_A A_(frak(q))$ 的消没可以铺开。把 $A$ 换成某个 $A_f$（$f in A - frak(q)$），不妨设 $Omega_(A\/k) = 0$。此时条件 (1) 说明 $X = Spec(A)$ 是 Artin 的且既约，从而 $X = union.sq.big_i Spec(L_i)$，其中 $L_i\/k$ 是有限多个有限可分扩张。 

    先看 $k$ 是代数闭域的情形。由 (2) $<==>$(3)，$Omega_(A\/k)$ 消没其实等价于对角态射 $Delta_(A\/k): Spec(A) -> Spec(A otimes_k A)$ 是开浸入。仿射态射都是闭映射，故它也是闭浸入。于是对任意闭点 $x in X$，包含映射 $x: Spec(k) -> X$ 的图 $Gamma_x: Spec(k) -> Spec(k) times_k X$ 作为对角态射的基变换，必是既开又闭的浸入。因此包含映射 $x -> X$ 本身也是既开又闭的浸入。换言之，$X$ 的每个闭点既开又闭。于是 $X$ 是它各个点的不交并。最后，由下面的引理，$X$ 既约，从而是若干 $Spec(k)$ 的不交并。这样 $k$ 代数闭的情形就证完了。 

    #lemma[
      设 $(A, frak(m))$ 是 Artin 局部环，在代数闭域 $k$ 上有限，且 $Omega_(A\/k) = 0$。则 $A = k$。 
    ]
    #proof[
      设 $g: k -> A$ 是结构映射，$epsilon: A -> k$ 是约化映射。定义： 
      $
        delta: A -> frak(m)\/frak(m)^2, a |-> [a - g(epsilon(a))]
      $
      则 $delta(g(x)) = 0$，且： 
      $
        delta(a b) = [(a - g(epsilon(a))) b + g(epsilon(a)) (b - g(epsilon(b)))] = epsilon(a) delta(b) + epsilon(b) delta(a) in frak(m)\/frak(m)^2
      $
      因此 $delta$ 是 $k$-导子。然而 $Omega_(A\/k) = 0$ 迫使 $delta = 0$。于是对每个 $a in frak(m)$，$a = a - g(epsilon(a)) in frak(m)^2$，从而 $frak(m) = frak(m)^2$。由 Nakayama 引理，这迫使 $frak(m) = 0$。 
    ]

    现在回到一般情形。$Omega_(A otimes_k ol(k)\/ol(k)) = Omega_(A\/k) otimes_k ol(k) = 0$，故 $A otimes_k ol(k)$ 是有限多个 $ol(k)$ 的积。特别地，数一下维数便知 $A$ 在 $k$ 上有限，从而是 Artin 的。又因 $A$ 几何既约，故它既约。于是 
    $
      Spec(A) = union.sq.big_i Spec(L_i)
    $
    其中 $L_i\/k$ 是某些有限域扩张。若 $"char"(k) = 0$，可分性自动成立。若 $"char"(k) = p$，取 $k$ 在 $L_i$ 中的可分闭包 $E_i$。则 $L_i = E_i [x_1, dots.c, x_m]\/(x_1^(p^(a_1)) - e_1, dots.c, x_m^(p^(a_m)) - e_m)$。由可分性有 $E_i otimes_k ol(k) = ol(k)^([E_i:k])$，故： 
    $
      L_i otimes_k ol(k) cong ((ol(k)[x_1, dots.c, x_m])/((x_1^(p^(a_1)) - e_1, dots.c, x_m^(p^(a_m)) - e_m)))^([E_i:k])
    $
    其各分支都是 $ol(k)$ 的幂零加厚。于是 $L_i otimes_k ol(k)$ 有 $[E_i:k]$ 个连通分支。另一方面，如我们所证 $L_i otimes_k ol(k) cong ol(k)^([L_i:k])$。因此 $[E_i:k] = [L_i:k]$，$E_i = L_i$，从而 $L_i\/k$ 可分。 
  ]
]

#definition(name: <defn-unramified-and-etale-morphisms>)[
  设 $f: X -> Y$ 局部有限展示，我们定义： 
  // #set enum(numbering: "(a)")
  + 若上述条件 (1)--(3) 对 $x$ 成立，则称 $f$ 在 $x$ 处*非分歧* (unramified)（这里采用 @cite-EGA4 的意义）。

  + 若 $f$ 在 $x$ 处非分歧，且局部同态 $cal(O)_(Y,f(x)) -> cal(O)_(X,x)$ 平坦（即 $f$ 在 $x$ 处平坦），则称 $f$ 在 $x$ 处*平展*。 

  + 若 $f$ 在每个 $x in X$ 处都非分歧/平展，则称 $f$ *非分歧/平展*。 

  #remark[
    我们关于非分歧性的定义取自 @cite-SGA4。有些文献把非分歧态射定义为局部有限型加 $Omega_(X\/Y) = 0$。

    当 $X, Y$ 是 Noether 概形时，两种定义没有区别；但后者比我们的定义略弱，因为我们的定义要求有限展示。 
  ]
]

#properties(name: <etale-first-props>)[
  (基本性质)

  0. 非分歧/平展性对底与源都是局部的。 

  + 有限展示的局部浸入是非分歧的。开浸入是平展的。 

  + 非分歧/平展态射在复合与基变换下都稳定。 

  + 给定态射 $X overset(->,f) Y overset(->,g) Z$，有： 
    + $g compose f$ 非分歧 $==>$ $f$ 非分歧； 
    + $g compose f$ 平展且 $g$ 非分歧 $==>$ $f$ 平展。 
]
#proof[
  (0) 由定义直接得到。 

  (2) 平坦性在基变换与复合下都保持，故只需证明非分歧性也保持。由局部性，不妨设所涉及的概形都是仿射的。基变换下的稳定性来自： 
  $
    Omega_(B'\/A') cong Omega_(B\/A) otimes_A A' #[其中] B' = B otimes_A A'
  $
  复合下的稳定性则来自 Kähler 微分的第一个正合序列（@cite-matsumura-ca[Theorem 57]）：
  $
    Omega_(B\/A) otimes_B C -> Omega_(C\/A) -> Omega_(C\/B) -> 0
  $
  其中第一项与第三项消没可推出第二项消没。 

  (1) 由局部性与 (2)，只需证明 $id$ 平展、闭浸入非分歧。$id$ 显然平展。闭浸入非分歧：在映射 $A ->> A\/I$ 之下，乘法映射 $mu: A\/I otimes_A A\/I -> A\/I$ 是同构 $A\/I otimes_A A\/I cong A\/I$，其核为 $0$，故 $Omega_((A\/I)\/A) = 0$。 

  (3a) 由局部性，不妨设所涉及的概形都是仿射的。考虑 Kähler 微分的第一个正合序列：
  $
    Omega_(B\/A) otimes_B C -> Omega_(C\/A) -> Omega_(C\/B) -> 0
  $
  第一项与第二项消没可推出第三项消没。 

  (3b) 这个证明应当是机械的：你只需用基变换与图概形，就像证明分离性与紧合性的类似性质时那样。考虑拉回图表： 
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYIl0sWzAsMiwiWSJdLFsyLDIsIlkgdGltZXNfWiBZIl0sWzIsMCwiWCB0aW1lc19aIFkiXSxbMCwxLCJmIl0sWzEsMiwiRGVsdGFfKFlcXC9aKSJdLFszLDIsImYgdGltZXMgaWRfWSIsMl0sWzAsMywiR2FtbWFfZiIsMl1d
  #align(center, diagram({
    node((-1, -1), [$X$])
    node((-1, 1), [$Y$])
    node((1, 1), [$Y times_Z Y$])
    node((1, -1), [$X times_Z Y$])
    edge((-1, -1), (-1, 1), [$f$], label-side: left, "->")
    edge((-1, 1), (1, 1), [$Delta_(Y\/Z)$], label-side: left, "->")
    edge((1, -1), (1, 1), [$f times id_Y$], label-side: right, "->")
    edge((-1, -1), (1, -1), [$Gamma_f$], label-side: right, "->")
  }))
  由于 $g: Y -> Z$ 非分歧，$Delta_(Y\/Z)$ 局部是开浸入，从而平展。于是它的基变换 $Gamma_f$ 也平展。现在 $f$ 分解为 $X -->^(Gamma_f) X times_Z Y -->^(p_2) Y$。其中 $p_2$ 是 $g compose f: X -> Z$ 的基变换，故平展。于是 $f$ 是两个平展态射的复合，从而平展。 
]

#example[
  (非分歧态射的例子)

  + 给定 $QQ$ 的有限扩张链 $L\/K\/QQ$： 
    $
      f: Spec(cal(O)_L) -> Spec(cal(O)_K)
    $
    这个 $f$ 是平坦的。我们要判断它是否非分歧：$f$ 在 $frak(q)$ 处非分歧，指的是取 $frak(p) = frak(q) ∩ cal(O)_K$ 之后，$cal(O)_(L,frak(q))\/frak(p) cal(O)_(L,frak(q))$ 是 $cal(O)_K \/ frak(p)$ 的有限可分扩张，而后者是有限域。 

    有限域的每个有限扩张都可分，故这等价于 $frak(p) cal(O)_(L,frak(q)) = frak(q) cal(O)_(L,frak(q))$，即 $e(frak(q)\/frak(p)) = 1$；也就是说，就数域的素位而言，$frak(q)$ 在 $frak(p)$ 之上非分歧。 

  + 设 $X = Spec(B) cong AA_k^1$，$B = k[x]$；$Y = Spec(A) cong AA_k^1$，$A = k[y]$。用 $k[y] -> k[x], y |-> x^n$ 定义 $f: X -> Y$，这是 $n$ 次幂映射，其中 $n >= 2$。由于 $B$ 是有限自由 $A$-模，$f$ 平坦。现在： 
    $
      Omega_(B\/A) = (B d x)/((n x^(n-1) d x)) cong k[x]/((n x^(n-1)))
    $
    因此，若 $n in k^times$，则对任意 $a != 0 in k$，$f$ 在 $(x-a)$ 处平展。 

    无论如何，只要 $n>=2$，$f$ 在 $(x)$ 处就不平展。 
]

#example(name: <kummer-and-artin-schreier-coverings>)[
  (平展态射的例子) 平展态射（更确切地说，有限平展态射）最重要的例子之二是 *Kummer 覆叠* 与 *Artin–Schreier 覆叠*。 

  + (Kummer 覆叠) 设 $X$ 是概形，$n in cal(O)_X^times$。对函数 $x in cal(O)_X (X)^times$，Kummer 覆叠定义为： 
    $
      tilde(X) = SPec((cal(O)_X [t])/((t^n - x))) -> X
    $
    这个覆叠是局部自由的，从而平坦。局部地，它形如 $Spec(A[t]\/(t^n - x)) -> Spec(A)$。因此局部地 $Omega_(tilde(X)\/X)$ 形如：
    $
      (A[t] d t)/((t^n - x, n t^(n-1))) = 0      
    $
    因为 $n in A^times$ 且 $x in A^times$。于是 $tilde(X) -> X$ 非分歧，从而是平展的。 

  + (Artin–Schreier 覆叠) 设 $X$ 是 $FF_p$-概形。对函数 $x in cal(O)_X (X)$，Artin–Schreier 覆叠定义为： 
    $
      tilde(X) = SPec((cal(O)_X [t])/((t^p - t - x))) -> X
    $
    这个覆叠是局部自由的，从而平坦。局部地，它形如 $Spec(A[t]\/(t^p - t - x)) -> Spec(A)$。因此局部地 $Omega_(tilde(X)\/X)$ 形如：
    $
      (A[t] d t)/((t^p - t - x, -1)) = 0      
    $
    于是 $tilde(X) -> X$ 非分歧，从而平展。 
]

#proposition[
  平展态射是开的，且拟有限。 
]
#proof[
  平展态射是开的，因为平坦态射是开的。（Noether 情形可按 @cite-hartshorne-ag[Exercise III.9.1] 验证。一般情形先化到仿射开集，再用 @absolute-noetherian-approx 与 @passage-to-limit-of-properties (a) 中的极限论证化归到 Noether 情形。）
  
  它们拟有限，因为纤维是平展的。现在若 $k$ 是域，则按非分歧性的定义，任何非分歧 $k$-概形 $X$ 都必形如： 
  $
    X = union.sq.big_i Spec(L_i), L_i\/k #[有限可分]
  $
  因而是离散的。于是每个平展态射的纤维都离散，故拟有限。 
]

接下来我们证明，许多良好的性质在平展态射下保持不变。 

#theorem(name: <etale-local-properties>)[
  设 $f: X -> Y$ 是在 $x$ 处平展的态射，$y = f(x)$。则下列性质中任何一条对 $cal(O)_(X,x)$ 成立，当且仅当同一条性质对 $cal(O)_(Y,y)$ 成立： 

  0. Noether 的（此时 $dim(cal(O)_(X,x)) = dim(cal(O)_(Y,y))$)； 
  + 正则； 
  + 具有 Serre 性质 $(R_k)$；
  + 具有 Serre 性质 $(S_k)$； 
  + 既约；
  + 正规。 
]
#proof[
  我们先证明一个引理，后面许多反向陈述都要用到它。 

  #lemma(name: <noetherianity-normality-descends-along-faithfully-flat-map>)[
    设 $A -> B$ 是忠实平坦 (faithfully flat) 态射。则： 

    + 若 $B$ 是 Noether 的，则 $A$ 是 Noether 的； 

    + 若 $B$ 正规，则 $A$ 正规。 
  ]
  #proof[
    (1) 对任意理想 $I subset A$，$I B subset B$ 有限生成，设由 $a_1, dots.c, a_n in I$ 生成。则由忠实平坦性， 
    $
      I = I B inter A = (a_1, dots.c, a_n) B inter A = (a_1, dots.c, a_n)
    $
    从而 $I$ 有限生成。 

    (2) 若 $B$ 正规，由于 $A -> B$ 是单射，$A$ 至少是整环。现在任取在 $A$ 上整的 $a\/b in Frac(A)$，把它看作 $Frac(B)$ 的元素，它在 $B$ 上整，故 $a\/b in B$。于是 $a in A inter b B$。但由忠实平坦性，$A inter b B = b A$，故 $a\/b in A$。因此 $A$ 正规。 
  ]

  沿 $Spec(cal(O)_(Y,y)) -> Y$ 对 $f$ 作基变换，不会改变 $x$ 与 $y$ 处的局部环。于是作此基变换，再把 $X$ 在 $x$ 附近缩小，不妨设 $f: Spec(B) = X -> Y = Spec(A)$ 是两个仿射概形之间的平展态射，$A$ 是局部环，$y$ 是 $Spec(A)$ 的闭点。 

  (0) 若 $cal(O)_(Y,y)$ 是 Noether 的，则 $cal(O)_(X,x)$ 作为 $cal(O)_(Y,y)$ 上的本质有限展示代数，必定也是 Noether 的。反向的论证与 @noetherianity-normality-descends-along-faithfully-flat-map (1) 中的论证完全相同；这里 $cal(O)_(Y,y) -> cal(O)_(X,x)$ 忠实平坦。 
  
  设 $cal(O)_(X,x)$ 是 Noether 的。对任意理想 $I subset cal(O)_(Y,y)$，$I cal(O)_(X,x)$ 作为 $cal(O)_(X,x)$ 的理想有限生成，设由 $f_1, dots.c, f_n in I$ 生成。由于 $cal(O)_(Y,y) -> cal(O)_(X,x)$ 忠实平坦，$I = cal(O)_(Y,y) inter I cal(O)_(X,x) = cal(O)_(Y,y) inter (f_1, dots.c, f_n) cal(O)_(X,x) = (f_1, dots.c, f_n)$。故 $I$ 有限生成，这就证明了 $cal(O)_(Y,y)$ 是 Noether 的。 
  
  至于维数，由于 $cal(O)_(Y,y) -> cal(O)_(X,x)$ 平坦，由 #cite-stacks("00ON")[Lemma 10.112.7]， 
  $
    dim(cal(O)_(X,x)) = dim(cal(O)_(Y,y)) + dim(cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x))
  $
  由平展性，$cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x) cong k(x)$ 是零维的，故 $dim(cal(O)_(X,x)) = dim(cal(O)_(Y,y))$。深度也有类似的公式（#cite-stacks("0337")[Lemma 10.163.2]）： 
  $
    "depth"(cal(O)_(X,x)) = "depth"(cal(O)_(Y,y)) + "depth"(cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x)) = "depth"(cal(O)_(Y,y))
  $
  其中 $"depth"(cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x)) = "depth"(k(x)) = 0$。 

  对于 (1)(2)(3)，由 (0) 不妨设 $cal(O)_(X,x)$ 与 $cal(O)_(Y,y)$ 都是 Noether 的，且有相同的维数 $d$。 

  (1) 设 $f_1, dots.c, f_t$ 是 $frak(m)_y$ 的极小生成集。由平展性，$frak(m)_x = frak(m)_y cal(O)_(X,x)$。故 $f_1, dots.c, f_t$ 也是 $frak(m)_x$ 的极小生成集。因此， 
  $
    dim_(k(y)) (frak(m)_y\/frak(m)_y^2) = t = dim_(k(x)) (frak(m)_x\/frak(m)_x^2)
  $
  于是 $cal(O)_(X,x)$ 与 $cal(O)_(Y,y)$ 的正则性都等价于 $t = d$，故二者等价。 

  (2) 对任意位于 $frak(p) in Spec(A)$ 之上的 $frak(q) in Spec(cal(O)_(X,x))$，由 (0)， 
  $
    dim(B_(frak(q))) = dim(A_(frak(p)))
  $
  故 $dim(B_(frak(q))) <= k$ 当且仅当 $dim(A_(frak(p))) <= k$。又由 (1)，$B_(frak(q))$ 与 $A_(frak(p))$ 的正则性等价。因此 $cal(O)_(X,x)$ 满足 ($R_k$) 当且仅当 $A$ 满足。 

  (3) 对任意位于 $frak(p) in Spec(A)$ 之上的 $frak(q) in Spec(cal(O)_(X,x))$，由维数与深度的公式， 
  $
    "depth"(B_(frak(q))) = "depth"(A_(frak(p)))
  $
  以及： 
  $
    min(k, dim(B_(frak(q)))) = min(k, dim(A_(frak(p))))
  $
  于是两个等式的左端相等当且仅当它们的右端相等。对所有 $frak(q)$ 用这一点，便知 $cal(O)_(X,x)$ 满足 ($S_k$) 当且仅当 $A$ 满足。 

  对于 (4)(5)，当 $A = cal(O)_(Y,y)$ 是 Noether 环时，则有 Serre 判别法： 

  - 既约性 $<==> (R_0) and (S_1)$；
  - 正规性 $<==> (R_1) and (S_2)$。 

  于是在 Noether 情形，(2)(3) 蕴涵 (4)(5)。一般情形要用极限论证。把 $A$ 写成 $A = dirlim_lambda A_lambda$，其中每个 $A_lambda$ 由 $A$ 的一个有限型 $ZZ$-子代数 $A_(lambda,0)$ 在 $A_(lambda,0) inter frak(m)_A$ 处局部化得到，指标按包含关系排序。由 @passage-to-limit-of-morphisms (1)，存在某个有限阶段 $lambda_0$ 与一个 $A_(lambda_0)$-代数 $B_(lambda_0)$，使得 $B cong B_(lambda_0) otimes_(A_(lambda_0)) A$。令 $B_lambda = B_(lambda_0) otimes_(A_(lambda_0)) A_lambda$。由 @passage-to-limit-of-properties (3d)，把 $lambda_0$ 放大之后，不妨设 $B_(lambda_0)$ 是平展 $A_(lambda_0)$-代数。于是对每个 $lambda >= lambda_0$，$B_lambda$ 都是平展 $A_lambda$-代数。 
  
  由于 $B = B_lambda otimes_(A_lambda) A$ 而 $B_lambda$ 在 $A_lambda$ 上平坦，映射 $B_lambda -> B$ 也都是包含。于是有正向极限： 
  $
    A = dirlim_lambda A_lambda, B = dirlim_lambda B_lambda 
  $
  其中过渡映射都是单射。设 $x in X$ 对应素理想 $frak(q) in Spec(B)$，它拉回到 $frak(q)_lambda in Spec(B_lambda)$。则： 
  $
    B_(frak(q)) = dirlim_lambda B_(lambda,frak(q)_lambda)
  $
  其过渡映射也都是单射。现在： 

  - 既约性方面：$A$ 既约当且仅当每个 $A_lambda$ 既约（因为 $A$ 的幂零元正是各个 $A_lambda$ 的幂零元之并）。同样，$B$ 既约当且仅当每个 $B_(lambda,frak(q)_lambda)$ 既约。于是 (4) 由 Noether 情形推出。 

  - 正规性方面：一个方向由极限论证给出。设 $A$ 正规。把每个 $A_lambda$（已知是整环）换成它在 $A$ 中的整闭包，不妨设每个 $A_lambda$ 都正规。于是由 (5) 的 Noether 情形，每个 $B_(lambda,frak(q)_lambda)$ 都正规。由此容易验证极限 $B_(frak(q))$ 正规。 

  - 正规性的另一个方向可以直接验证。注意 $A -> C = B_(frak(q))$ 忠实平坦。于是若 $C$ 正规，便可引用 @noetherianity-normality-descends-along-faithfully-flat-map (2) 断定 $A$ 正规。 

  这样我们就证明了一般情形的 (4)(5)。 
]

平展性可以用 Jacobi 矩阵判定，如下面的引理所示。 
#lemma(name: <jacobian-criterion-for-etaleness>)[
  (平展性的 Jacobi 判别法) 设： 
  $
    B = A[T_1, dots.c, T_n]/((F_1, dots.c, F_n))
  $
  且 Jacobi 矩阵 $J = display(mat(nabla F_1, dots.c, nabla F_n))$ 在 $B$ 中可逆。则 $B$ 在 $A$ 上平展。 
]
#proof[
  首先， 
  $
    Omega_(B\/A) = (oplus.big_(i=1)^n B d T_i)/((d F_1, dots.c, d F_n)) = 0
  $
  故 $B$ 在 $A$ 上非分歧。于是只需证明平坦性。 
  // 可以取子环 $A_0 subset A$，它是有限型 $ZZ$-代数，使得每个 $F_i in A_0 [T_1, dots.c, T_n]$。令： 
  // $
  //   B_0 = (A_0 [T_1, dots.c, T_n])/((F_1, dots.c, F_n))
  // $
  // 把 $A_0$ 放大，使 $B_0$ 含有 Jacobi 矩阵 $J = display(mat(nabla F_1, dots.c, nabla F_n))$ 的行列式之逆，则不妨设 $J$ 在 $B_0$ 中可逆。于是把 $A, B$ 换成 $A_0, B_0$，不妨设 $A, B$ 都是 Noether 的。 
  先假设 $A$ 是 Noether 的。 
  
  固定位于 $frak(p) in Spec(A)$ 之上的 $frak(q) in Spec(B)$。平坦轨迹是开集，故只需在一个稠密点集上证明平坦性。于是不妨设 $frak(q)$ 是它在 $frak(p)$ 上的纤维中的闭点。令 $P = A[T_1,dots.c,T_n]$，并设 $frak(r) in Spec(P)$ 对应 $frak(q)$。我们要证 $A_(frak(p)) -> B_(frak(q))$ 平坦。注意 $B_(frak(q)) = P_(frak(r))\/(F_1, dots.c, F_n)$，且 $A_(frak(p)) -> P_(frak(r))$ 平坦。因此我们想用下面的平坦性判别法： 

  #lemma[
    (#cite-stacks("00MG")[Lemma 10.99.3]) 设 $A -> B$ 是 Noether 局部环之间的平坦局部同态，$f_1, dots.c, f_c in B$，且 $[f_1], dots.c, [f_c] in B\/frak(m)_A B$ 构成正则序列。则 $B\/(f_1, dots.c, f_c)$ 在 $A$ 上平坦。  
  ]

  按此判别法，注意：
  $
    P_(frak(r))\/frak(p) P_(frak(r)) = k(frak(p))[T_1, dots.c, T_n]_(ol(frak(r)))
  $
  其中 $ol(frak(r))$ 是 $frak(r)$ 的约化。由于 $frak(q)$ 是它在 $frak(p)$ 上的纤维中的闭点，$ol(frak(r))$ 是 $S = k(frak(p))[T_1, dots.c, T_n]$ 的极大理想。故右端是维数为 $n$ 的正则局部环。 
  
  于是只需证明这 $n$ 个元素 $ol(F)_1, dots.c, ol(F)_n in S = k(frak(p))[T_1, dots.c, T_n]$ 在这个 $n$ 维正则局部环 $S_(ol(frak(r)))$ 中构成正则序列。由于 $F_1, dots.c, F_n in frak(r)$，有 $ol(F)_1, dots.c, ol(F)_n in ol(frak(r)) S_(ol(frak(r)))$。 
  
  现在只需证明 $ol(F)_1, dots.c, ol(F)_n in ol(frak(r)) S_(ol(frak(r)))$ 在 $ol(frak(r)) S_(ol(frak(r)))\/ol(frak(r))^2 S_(ol(frak(r)))$ 中线性无关。考虑余切映射： 
  $
    ol(frak(r)) S_(ol(frak(r)))\/ol(frak(r))^2 S_(ol(frak(r))) &-> Omega_(S_(ol(frak(r)))\/k(frak(p))) \
    [F] &|-> d F
  $
  它把各元素映为： 
  $
    ol(F)_i |-> sum_(j=1)^n (partial ol(F)_i)/(partial T_j) d T_j
  $
  由于 Jacobi 矩阵 $mat(display((partial ol(F)_i)/(partial T_j)))$ 是 $J$ 的约化，它可逆。故 $d ol(F)_i$ 在 $Omega_(S_(ol(frak(r)))\/k(frak(p)))$ 中 $k(frak(p))$-线性无关。于是它们在 $ol(frak(r)) S_(ol(frak(r)))\/ol(frak(r))^2 S_(ol(frak(r)))$ 中也线性无关，从而构成 $S_(ol(frak(r)))$ 的正则序列。至此 $A$ 是 Noether 的情形证完。 

  一般情形：取有限型 $ZZ$-子代数 $A_0 subset A$，使每个 $F_i in A_0 [T_1, dots.c, T_n]$。此外，存在 $G_0, G_1, dots.c, G_n in A_0 [T_1, dots.c, T_n]$，使得： 
  $
    G_0 det(J) + sum_(i=1)^n G_i F_i = 1
  $
  则 $B_0 = A_0 [T_1,dots.c,T_n]\/(F_1,dots.c,F_n)$ 也满足假设，而 $A_0$ 是 Noether 的。故 $B_0$ 在 $A_0$ 上平展。于是 $B = B_0 otimes_(A_0) A$ 在 $A$ 上平展。 
]

接下来要定义光滑态射。我们需要证明光滑性的各种定义彼此等价，为此先准备几个引理。 

#lemma(name: <equiv-defns-of-smooth-auxiliary>)[
  设 $X$ 是域 $k$ 上的有限型概形，$x in X$。则： 
  $
    dim((Omega_(X\/k))_x otimes_(cal(O)_(X,x)) k(x)) >= d_x := dim(cal(O)_(X,x)) + trd_k (k(x))
  $
  这里右端也是 $X$ 中含 $x$ 的不可约分支的最大维数。 

  此外，等号成立当且仅当 $X$ 在 $x$ 的某个邻域内几何正则。此时 $Omega_(X\/k)$ 在 $x$ 附近局部自由。对任意局部展示 $X = Spec(A)$，$A = k[T_1, dots.c, T_n]\/I$，存在 $F_1, dots.c, F_(n-d_x) in I$ 在 $x$ 附近生成 $I$，以及坐标 $T_(j_1), dots.c, T_(j_(d_x))$，使得 Jacobi 矩阵 $J = display(mat(nabla F_1, dots.c, nabla F_(n-d_x), E_(j_1), dots.c, E_(j_(d_x)))) in MM_(n times n) (k[T_1, dots.c, T_n])$ 约化到 $A$ 后可逆。 
]
#proof[
  这个引理在 $x$ 附近是局部的，故可把 $X$ 在 $x$ 附近缩小，使 $X = Spec(A)$ 仿射。设 $x$ 对应素理想 $frak(p)$，则 $k(x) = A_(frak(p))\/frak(p) A_(frak(p))$。设 $phi_x: A -> k(x)$ 是求值映射。现在令： 
  $
    psi_x: A otimes_k ol(k(x)) -> ol(k(x)), a otimes u |-> phi_x (a) u
  $
  令 $frak(q) = ker(psi_x)$，$S = (A otimes_k ol(k(x)))_(frak(q))$。则 $S_(frak(q))\/frak(q) S_(frak(q)) = ol(k(x))$。进一步， 

  - $frak(q) in Spec(S)$ 位于 $frak(p) in Spec(A)$ 之上。此外，扩域不改变不可约分支的维数。因此， 
    $
      dim(S_(frak(q))) = max_(Z subset Spec(S) \ #[不可约分支]) dim(Z) = max_(Z subset Spec(A) \ #[不可约分支]) dim(Z) = d_x
    $

  - 另一方面，$frak(q) in Spec(S)$ 是 $ol(k(x))$-有理点。现在： 
    $
      Omega_(S\/ol(k(x))) = Omega_(A\/k) otimes_A S
    $
    在 $frak(q)$ 处局部化，得到： 
    $
      Omega_(S_(frak(q))\/ol(k(x))) = Omega_(A\/k) otimes_A S_(frak(q))
    $
    最后模去 $frak(q) S_(frak(q))$ 约化，得到： 
    $
      Omega_(S_(frak(q))\/ol(k(x))) otimes_(S_(frak(q))) ol(k(x)) &= Omega_(A\/k) otimes_A ol(k(x)) = Omega_(A_(frak(p))\/k) otimes_(A_(frak(p))) ol(k(x)) \
      &= (Omega_(A_(frak(p))\/k) otimes_(A_(frak(p))) k(x)) otimes_(k(x)) ol(k(x))
    $
    因此，
    $
    dim_(ol(k(x))) (Omega_(S_(frak(q))\/ol(k(x))) otimes_(S_(frak(q))) ol(k(x))) = dim_(k(x)) (Omega_(A_(frak(p))\/k) otimes_(A_(frak(p))) k(x))
    $
  另一方面，$frak(q) in Spec(S)$ 是有限型 $ol(k(x))$-概形 $Spec(S)$ 的有理点。由 @cite-hartshorne-ag[Proposition III.8.6]，$Omega_(S_(frak(q))\/ol(k(x))) cong frak(q) S_(frak(q))\/frak(q)^2 S_(frak(q))$。于是我们要证的不等式化为：
  $
    dim_(ol(k(x))) (frak(q) S_(frak(q))\/frak(q)^2 S_(frak(q))) >= dim(S_(frak(q)))
  $
  这正是比较局部环的维数与其极大理想的极小生成元个数的标准不等式。此外，若 $Spec(A)$ 在 $x$ 附近几何正则，则 $S_(frak(q))$ 就正则，上述不等式便取等号。反之，取一个展示： 
  $
    A = P\/I, P = k[T_1, dots.c, T_n]
  $
  并设 $frak(q) in Spec(P)$ 是 $frak(p) in Spec(A)$ 所对应的素理想。现在有第二个正合序列（@cite-matsumura-ca[Theorem 58]）： 
  $
    I\/I^2 -> Omega_(P\/k) otimes_P A -> Omega_(A\/k) -> 0
  $
  把它与 $k(x)$ 作张量积： 
  $
    I\/I^2 otimes_A k(x) -> oplus.big_(i=1)^n k(x) d T_i -> Omega_(A\/k) otimes_A k(x) -> 0
  $
  在等号成立的情形，$dim_(k(x)) (Omega_(A\/k) otimes_A k(x)) = d_x$。于是 $dim_(k(x)) (im(I\/I^2 otimes_A k(x)-> oplus.big_(i=1)^n k(x) d T_i)) = n - d_x$。因此可以取 $F_1, dots.c, F_(n-d_x) in I$，使 ${d F_i}$ 构成 $im(I\/I^2 otimes_A k(x)-> oplus.big_(i=1)^n k(x) d T_i)$ 的一组基。现在：
  $
    dim(P_(frak(q))) = dim(P) - dim(P\/frak(q)) = n - trd_k (Frac(P\/frak(q))) = n - trd_k (k(x))
  $
  $F_1, dots.c, F_(n-d_x)$ 在 $frak(q) P_(frak(q))\/frak(q)^2 P_(frak(q))$ 中的类 $k(x)$-线性无关，否则它们会在 $d F_1, dots.c, d F_(n-d_x)$ 之间诱导出一个 $k(x)$-线性关系。于是 $F_1, dots.c, F_(n-d_x)$ 可以扩充为正则局部环 $P_(frak(q))$ 的正则参数系，从而 $P_(frak(q))\/(F_1, dots.c, F_(n-d_x))$ 是正则局部环，其维数为： 
  $
    dim(P_(frak(q))\/(F_1, dots.c, F_(n-d_x))) = dim(P_(frak(q))) - (n - d_x) = d_x - trd_k (k(x)) = dim(cal(O)_(X,x))
  $
  另一方面，它满射到 $P_(frak(q))\/I P_(frak(q)) = cal(O)_(X,x)$，后者的维数同样是 $dim(cal(O)_(X,x))$。正则局部环的真商维数必定更小。因此只能有： 
  $
    I P_(frak(q)) = (F_1, dots.c, F_(n-d_x)) subset P_(frak(q))
  $
  现在取坐标 $T_(j_1), dots.c, T_(j_(d_x))$，使 $[d T_(j_i)]$ 构成 $coker(I\/I^2 otimes_A k(x)-> oplus.big_(i=1)^n k(x) d T_i)$ 的一组基。则 $d F_1, dots.c, d F_(n-d_x), d T_(j_1), dots.c, d T_(j_(d_x))$ 构成 $oplus.big_(i=1)^n k(x) d T_i$ 的一组基。 

  构造 Jacobi 矩阵：
  $
    J = mat(nabla F_1, dots.c, nabla F_(n-d_x), E_(j_1), dots.c, E_(j_(d_x))) in MM_(n times n) (P)
  $
  其中 $E_j$ 是第 $j$ 个标准基向量。由上面的讨论，$det(J) in P$ 约化到 $k(x)$ 中成为单位，从而在 $A_(frak(p))$ 中也是单位。由铺开，存在 $h in P$ 使 $det(J)$ 在 $A_h$ 中是单位。由于 $I P_(frak(q)) = (F_1, dots.c, F_(n-d_x)) subset P_(frak(q))$，把 $Spec(P_h)$ 在 $frak(q)$ 附近缩小，不妨设 $I P_h = (F_1, dots.c, F_(n-d_x)) subset P_h$。我们断言 $Spec(A_h)$ 几何正则。事实上， 
  $
    A_h = P_h\/I P_h = P_h\/(F_1, dots.c, F_(n-d_x)) = k[T_0, T_1, dots.c, T_n]\/(T_0 h - 1, F_1, dots.c, F_(n-d_x))
  $
  构造 Jacobi 矩阵：
  $
    J' &= mat(nabla (T_0 h - 1), nabla F_1, dots.c, nabla F_(n-d_x), E_(j_1), dots.c, E_(j_(d_x))) \
    &= mat(h, 0; T_0 nabla h, J) in MM_((n+1) times (n+1)) (P[T_0]) 
  $
  它在 $A_h$ 中可逆（因为 $h$ 与 $det(J)$ 都可逆）。把行列式展开，这说明这个展示的 Jacobi 矩阵 $display(mat(nabla (T_0 h - 1), nabla F_1, dots.c, nabla F_(n-d_x)))$ 删去第 $j_1, dots.c, j_(d_x)$ 行后，有一个 $(1+n-d_x) times (1+n-d_x)$ 的可逆子式。这个子式在基域 $k$ 的任意扩张下仍然可逆。于是为证几何正则性，只需证明： 

  #lemma(name: <jacobian-criterion-for-geom-regularity>)[
    设 $A$ 是有限型 $k$-代数，有展示 $A cong k[T_1, dots.c, T_n]\/(f_1, dots.c, f_m)$，$m <= n$。若 Jacobi 矩阵 $J = display(mat(nabla f_1, dots.c, nabla f_m))$ 有一个可逆的 $m times m$ 子式，则 $A$ 在 $k$ 上几何正则。 
  ]
  #proof[
    令 $P = k[T_1, dots.c, T_n], I = (f_1, dots.c, f_m)$。构造第二个正合序列： 
    $
      I\/I^2 -> Omega_(P\/k) otimes_P A -> Omega_(A\/k) -> 0
    $
    由那个可逆的 $m times m$ 子式，$d f_1, dots.c, d f_m$ 张成 $Omega_(P\/k) otimes_P A cong oplus.big_(i=1)^n A d T_i$ 的一个秩为 $m$ 的自由子模。于是对每个点 $frak(p) in Spec(A)$，$d f_1, dots.c, d f_m$ 张成 $oplus.big_(i=1)^n k(frak(p)) d T_i$ 的一个 $m$ 维子空间。
    
    现在设 $frak(p) in Spec(A)$ 是某个闭点 $frak(q) in Spec(P)$ 的像，则 $A_(frak(p)) = P_(frak(q))\/(f_1, dots.c, f_m)$。$f_1, dots.c, f_m$ 在 $frak(q) P_(frak(q))\/frak(q)^2 P_(frak(q))$ 中的类线性无关，否则它们会在 $d f_1, dots.c, d f_m$ 之间给出一个 $k(frak(p))$-线性关系。于是 $f_1, dots.c, f_m$ 可以扩充为 $n$ 维正则局部环 $P_(frak(q))$ 的正则参数系。故 $A_(frak(p)) = P_(frak(q))\/(f_1, dots.c, f_m)$ 正则。对 $k$ 的任意域扩张，同样的论证都适用，因为 Jacobi 子式仍然可逆；因此 $A$ 在 $k$ 上几何正则。 
  ]

  至于 $Omega_(A\/k)$ 的局部自由性，对于这样的展示， 
  $
    Omega_(A\/k) = (A d T_1 oplus dots.c oplus A d T_n)/((d f_1, dots.c, d f_m))
  $
  由那个可逆的 Jacobi 子式，它在 $A$ 上局部自由，秩为 $n - m$。 
]

#proposition(name: <equiv-defns-of-smooth>)[
  设 $f: X -> Y$ 是局部有限展示的态射。对 $y = f(x)$，下列条件等价： 

  + $f$ 在 $x$ 处平坦，且：#h(1fr)
    $
      dim_(k(x)) ((Omega_(X\/Y))_x otimes_(cal(O)_(X,x)) k(x)) = dim(cal(O)_(X_y,x)) + trd_(k(y)) (k(x))
    $
    其中右端也是 $x in X_y$ 的充分小开邻域的维数。这里的等号可以放宽为 $<=$。 

  + $f$ 在 $x$ 处平坦，且 $X_y$ 在 $x$ 附近几何正则。 

  + 存在开邻域 $x in U subset X$，以及分解 $f|_U: U ->^j AA^d_Y -> Y$，其中 $j$ 平展。 

  + 对任意仿射开集 $x in Spec(B) subset X$、$y in Spec(A) subset Y$，以及任意展示 $B cong P\/I, P = A[T_1, dots.c, T_n]$，第二个正合序列： 
    $
      I\/I^2 -> Omega_(P\/A) otimes_P B -> Omega_(B\/A) -> 0
    $
    它先验地只是右正合，实际上在 $x$ 处的茎上分裂正合。 

  + 对某组仿射开集 $x in Spec(B) subset X$、$y in Spec(A) subset Y$，以及某个展示 $B cong P\/I, P = A[T_1, dots.c, T_n]$，第二个正合序列： 
    $
      I\/I^2 -> Omega_(P\/A) otimes_P B -> Omega_(B\/A) -> 0
    $
    它先验地只是右正合，实际上在 $x$ 处的茎上分裂正合。 
  
  在这些条件下，$Omega_(X\/Y)$ 在 $x$ 处局部自由，秩为 $d$。 
]
#proof[
  @equiv-defns-of-smooth-auxiliary 立即给出 (1) $<==>$(2)，因为： 
  $
    (Omega_(X\/Y))_x otimes_(cal(O)_(X,x)) k(x) &cong Omega_(cal(O)_(X,x)\/cal(O)_(Y,y)) otimes_(cal(O)_(X,x)) k(x) \
    &cong Omega_(cal(O)_(X,x)\/cal(O)_(Y,y)) otimes_(cal(O)_(X,x)) cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x) otimes_(cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x)) k(x) \
    &cong Omega_(cal(O)_(X_y,x)\/k(y)) otimes_(cal(O)_(X_y,x)) k(x)
  $

  接下来证明 (3) $==>$(2)。事实上，把 $X$ 在 $x$ 附近缩小，便得到分解： 
  $
    f: X ->^j AA^d_Y -> Y
  $
  其中 $j$ 平展。于是对任意域扩张 $L\/k(y)$，纤维上有映射 $(X_y)_L -> AA^d_L -> L$，且 $(X_y)_L\/AA^d_L$ 平展。由于 $AA^d_L$ 正则，由 @etale-local-properties (1)，$(X_y)_L$ 正则。故 $X_y$ 几何正则。平坦性由平展性得到。 

  下面证明 (1)(2) $==>$(3)，从而建立 (1)(2)(3) 的等价性。 
  
  #proof[
    所涉及的性质在 $x$ 与 $y$ 附近都是局部的，故不妨设 $Y = Spec(A)$，$y$ 对应素理想 $frak(p)$；$X = Spec(B)$，$x$ 对应 $frak(q)$。令 $ol(B) = B_(frak(p))\/frak(p) B_(frak(p))$，使 $X_y = Spec(ol(B))$，并设 $ol(frak(q)) in Spec(ol(B))$ 对应 $frak(q)$。 
  
    由 @equiv-defns-of-smooth-auxiliary，$Omega_(ol(B)\/k(y))$ 在 $ol(frak(q))$ 处局部自由、秩为 $d$；并且把 $B$ 的谱在 $ol(frak(q))$ 附近缩小后，$ol(B)$ 是 $k(y)$ 上维数为 $d$ 的几何正则概形，且其谱连通。特别地，$ol(B)$ 至少是维数为 $d$ 的正则整环。 
    
    取 $ol(b)_i in ol(B)_(ol(frak(q)))$，使 $[d ol(b)_1], dots.c, [d ol(b)_d]$ 构成 $Omega_(ol(B)_(ol(frak(q)))\/k(y)) otimes_(ol(B)_(ol(frak(q)))) k(x)$ 的一组基。由 Nakayama 引理，$Omega_(ol(B)_(ol(frak(q))\/k(y))$ 由 $d ol(b)_1, dots.c, d ol(b)_d$ 生成。接着把 $ol(b)_i$ 任意提升为 $b_i in B_(frak(q))$，则： 
    $
      Omega_(ol(B)_(ol(frak(q)))\/k(y)) = Omega_(B_(frak(q))\/A_(frak(p))) otimes_(B_(frak(q))) B_(frak(q))\/frak(p) B_(frak(q))
    $
    它由元素 $[d b_1], dots.c, [d b_d]$ 生成。现在 $frak(p) B_(frak(q)) subset frak(q) B_(frak(q))$，故由 Nakayama 引理，$Omega_(B_(frak(q))\/A_(frak(p)))$ 由 $d b_1, dots.c, d b_d$ 生成。换言之，$(Omega_(B\/A))_(frak(q))$ 由 $d b_1, dots.c, d b_d$ 生成。 
    
    由于 $b_i in B_(frak(q))$，把 $Spec(B)$ 在 $frak(q)$ 附近缩小，不妨设每个 $b_i in B$ 都是整体截面。这些截面通过求值定义映射： 
    $
      phi: P = A[T_1, dots.c, T_d] -> B
    $
    从而给出分解 $Spec(B) -> Spec(P) = AA^d_A -> Spec(A)$。考虑相对微分的第一个正合序列： 
    $
      Omega_(P\/A) otimes_P B -> Omega_(B\/A) -> Omega_(B\/P) -> 0
    $
    第一个映射是 $d T_i |-> d b_i$。于是把 $B$ 在 $frak(q)$ 处局部化后，$Omega_(P\/A) otimes_P B -> Omega_(B\/A)$ 满射。再把 $Spec(B)$ 在 $frak(q)$ 附近缩小，不妨设此映射满射。于是 $Omega_(B\/P) = 0$，故 $B$ 在 $P$ 上非分歧。把 $B$ 的谱在 $frak(q)$ 附近进一步缩小，不妨设 $B$ 在 $A$ 上平坦。 

    #lemma[
      设 $k$ 是域，$X, Y$ 是同维数的连通正则有限型 $k$-概形，$f: X -> Y$ 是非分歧态射。则 $f$ 平展。 
    ]
    #proof[
      $X, Y$ 作为正则连通 Noether 概形都是整环。 // 由于 $f$ 支配，$X$ 的泛点位于 $Y$ 的泛点之上，故 $K(X)\/K(Y) $ 是有限可分扩张。于是 $dim(X) = trd_k (K(X)) = trd_k (K(Y)) = dim(Y) $。 
      
      对任意闭点 $x in X$，$y = f(x) in Y$ 是闭点。现在 $cal(O)_(X,x), cal(O)_(Y,y)$ 都是正则局部环。由奇迹平坦性（#cite-stacks("00R4")[Lemma 10.128.1]），只需验证： 
      $
        dim(cal(O)_(X,x)) = dim(cal(O)_(Y,y)) + dim(cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x))
      $
      由非分歧性，$dim(cal(O)_(X,x)\/frak(m)_y cal(O)_(X,x)) = dim(k(x)) = 0$。由于 $x, y$ 分别是 $X, Y$ 的闭点， 
      $
        dim(cal(O)_(X,x)) = dim(X) = dim(Y) = dim(cal(O)_(Y,y))
      $
      这样便证明了 $f$ 在 $X$ 的每个闭点处平坦。由于平坦轨迹是开集，$f$ 平坦。 
    ]

    现在： 

    - 按假设 $B$ 在 $A$ 上平坦，而 $P = A[T_1,dots.c,T_d]$ 也在 $A$ 上平坦。 

    - 纤维上的映射 $k(y)[T_1, dots.c, T_d] -> ol(B)$ 已知非分歧。按假设 $ol(B)$ 是维数为 $d$ 的正则整环。$k(y)[T_1, dots.c, T_d]$ 当然是正则整环。现在： 

      $
        dim(ol(B)) = d = dim(k(y)[T_1, dots.c, T_d])
      $

      于是由上面的引理，$k(y)[T_1, dots.c, T_d] -> ol(B)$ 平展。 

    于是由平坦性的逐纤维判别法（#cite-stacks("039C")[Theorem 37.16.2]），$B$ 在 $frak(q)$ 处在 $P$ 上平坦。再把 $B$ 在 $frak(q)$ 附近缩小一次，$Spec(B) -> AA^d_A$ 就平展了。 #suppress-qed
  ]
  这样便得到 (1)(2)(3) 的等价性。 

  (1)(2)(3) $==>$(4)： 

  #proof[
    不妨设 $Y = Spec(A)$，$y$ 对应素理想 $frak(p)$；$X = Spec(B)$，$x$ 对应 $frak(q)$。由铺开平坦性，不妨设 $B$ 在 $A$ 上平坦。令 $ol(B) = B_(frak(p))\/frak(p) B_(frak(p))$，使 $X_y = Spec(ol(B))$，并设 $ol(frak(q)) in Spec(ol(B))$ 对应 $frak(q)$。 

    任取展示 $B = P\/I$，$P = A[T_1, dots.c, T_n]$。约化到 $ol(B)$，得到展示： 
    $
      ol(B) = k(y)[T_1, dots.c, T_n]\/ol(I)
    $
    由 @equiv-defns-of-smooth-auxiliary，把 $Spec(B)$ 适当缩小后，不妨设 $ol(I) = (ol(F)_1, dots.c, ol(F)_(n-d))$，且 $ol(J) = display(mat(nabla ol(F)_1, dots.c, nabla ol(F)_(n-d)))$ 有一个在 $ol(B)$ 上可逆的 $(n-d) times (n-d)$ 子式。不失一般性，可设： 
    $
      det mat(display((partial ol(F)_j)/(partial T_i)))_(1<=i,j<=n-d) in ol(B)^times
    $
    现在考虑正合序列 $0 -> I -> P -> B -> 0$。把 $- otimes_A k(y)$ 作用上去，得到： 
    $
      "Tor"_1^A (k(y), B) -> I_(frak(p))\/frak(p) I_(frak(p)) -> k(y)[T_1, dots.c, T_n] -> ol(B) -> 0
    $
    现在 $B$ 在 $A$ 上平坦，故 Tor 项消没。于是 $ol(I) = I_(frak(p))\/frak(p) I_(frak(p))$。任取 $ol(F)_i$ 的提升 $F_i in I_(frak(p))$，它们必定属于某个 $I_h$（$h in A$）。于是把 $A$ 的谱缩小，不妨设已取到提升 $F_i in I$。令 $N = I\/(F_1, dots.c, F_(n-d))$，并设 $frak(r) in Spec(P)$ 对应 $frak(q) in Spec(B)$。则： 
    $
      N_(frak(r))\/frak(p) N_(frak(r)) = (N_(frak(p))\/frak(p) N_(frak(p)))_(frak(r)) = 0
    $ 
    这是因为 $ol(I) = (ol(F)_1, dots.c, ol(F)_(n-d))$，从而 $I_(frak(p)) = (F_1, dots.c, F_(n-d)) + frak(p) I_(frak(p))$。现在 $I$ 是有限生成理想，故 $I$ 是有限 $P$-模。于是 $N_(frak(r))$ 是有限 $P_(frak(r))$-模，可以应用 Nakayama 引理，得 $N_(frak(r)) = 0$，从而： 
    $
      I_(frak(r)) = (F_1, dots.c, F_(n-d))
    $
    因此再把 $Spec(B)$ 在 $frak(q)$ 附近缩小，可以安排提升 $F_i in I$ 使得 $I = (F_1, dots.c, F_(n-d))$。我们知道： 
    $
      det mat(display((partial F_j)/(partial T_i)))_(1<=i,j<=n-d) mod frak(p) B_(frak(p)) = det mat(display((partial ol(F)_j)/(partial T_i)))_(1<=i,j<=n-d) in ol(B)^times
    $
    因此这个行列式（作为 $B$ 的元素）至少落在 $frak(q)$ 之外。把这个行列式求逆，再把 $Spec(B)$ 在 $frak(q)$ 附近缩小一次，不妨设： 
    $
      det(H) in B^times, H := mat(display((partial F_j)/(partial T_i)))_(1<=i,j<=n-d)
    $
    并令 $H^(-1) = display(mat(G_(i,j))) in GL_(n-d) (B)$。 

    现在考虑第二个正合序列： 
    $
      I\/I^2 -> oplus.big_(i=1)^n B d T_i -> Omega_(B\/A) -> 0
    $
    我们构造 $delta: I\/I^2 -> oplus.big_(i=1)^n B d T_i$ 的左逆，使该序列分裂正合。事实上，令： 
    $
      lambda: oplus.big_(i=1)^n B d T_i &-> I\/I^2 \
      d T_i &|-> sum_(j=1)^(n-d) G_(j,i) F_j, forall i <= n - d \
      d T_i &|-> 0, forall i > n-d
    $
    则对 $i <= n-d$： 
    $
      lambda(delta(F_i)) &= lambda(sum_(j=1)^(n-d) (partial F_i)/(partial T_j) d T_j) = sum_(j=1)^(n-d) sum_(k=1)^(n-d) (partial F_i)/(partial T_j) G_(j,k) F_k \
      &= sum_(k=1)^(n-d) F_k (sum_(j=1)^(n-d) (partial F_i)/(partial T_j) G_(k,j)) = sum_(k=1)^(n-d) F_k delta_(i,k) = F_i
    $
    这样我们就使这个正合序列分裂了。 

    #suppress-qed
  ]
  
  (4) $==>$(5) 是同义反复，故剩下要证 (5) $==>$(3)。  
  #proof[
    不妨设 $y$ 对应素理想 $frak(p)$，$x$ 对应 $frak(q)$。在展示 $B = P\/I, P = A[T_1,dots.c,T_n]$ 中，设 $frak(q)$ 对应素理想 $frak(r) in Spec(P)$。 
    
    令 $ol(B) = B_(frak(p))\/frak(p) B_(frak(p))$，使 $X_y = Spec(ol(B))$，并设 $ol(frak(q)) in Spec(ol(B))$ 对应 $frak(q)$。 

    把分裂正合序列铺开，不妨设： 
    $
      0 -> I\/I^2 -> oplus.big_(i=1)^n B d T_i -> Omega_(B\/A) -> 0
    $
    是分裂正合的。于是 $I\/I^2$ 与 $Omega_(B\/A)$ 都是局部自由 $B$-模；再把 $Spec(B)$ 缩小，不妨设它们分别自由，秩为 $n-d$ 与 $d$。取 $F_1, dots.c, F_(n-d) in I$，使它们构成 $I\/I^2$ 的一组 $B$-基。现在： 
    $
      I_(frak(r)) = (F_1, dots.c, F_(n-d)) + I_(frak(r))^2 subset (F_1, dots.c, F_(n-d)) + frak(r) I_(frak(r))
    $
    由 Nakayama 引理，$I_(frak(r)) = (F_1, dots.c, F_(n-d))$。于是把 $Spec(B)$ 在 $frak(q)$ 附近再缩小，不妨设 $I = (F_1, dots.c, F_(n-d))$。映射： 
    $
      delta: I\/I^2 = oplus.big_(i=1)^(n-d) B [F_i] &-> oplus.big_(i=1)^n B d T_i \
      F_i &|-> sum_(j=1)^n (partial F_i)/(partial T_j) d T_j
    $
    它有左逆。于是 Jacobi 矩阵 $J = display(mat(nabla F_1, dots.c, nabla F_(n-d)))$ 有左逆。故 $J$ 的某个 $(n-d) times (n-d)$ 子式的行列式在 $k(x)$ 中可逆，也就是在 $B - frak(q)$ 中可逆。再把 $Spec(B)$ 在 $frak(q)$ 附近缩小一次，不妨设 $J$ 的某个 $(n-d) times (n-d)$ 子式在 $B$ 中可逆，比如第一个。 // 由 @jacobian-criterion-for-geom-regularity，$Spec(B) -> Spec(A) $ 的纤维几何正则，维数为 $d$。 
    
    现在作分解： 
    $
      Spec(B) ->^j Spec(A[T_(n-d+1), dots.c, T_n]) -> Spec(A)
    $
    我们要证 $j$ 平展。这由平展性的 Jacobi 判别法 @jacobian-criterion-for-etaleness 立得。
    #suppress-qed
  ]
  至此我们证明了 (1)-(5) 的等价性。 
]

#definition(name: <defn-smooth-morphisms>)[
  设 $f: X -> Y$ 局部有限展示。若 $f$ 在 $x$ 处满足上面的 (1)-(5)（其中 $d$ 取条件 (3) 中的相对维数），则称 $f$ 在 $x$ 处*光滑（相对维数为 $d$）*。 
  
  若 $f$ 在 $X$ 的每一点处都光滑（相对维数为 $d$），则称 $f$ *光滑（相对维数为 $d$）*。 
]

#properties[
  0. 光滑性（相对维数为 $d$）对源是 Zariski 局部的。 

  + 一个态射平展，当且仅当它光滑且相对维数为 $0$。 

  + 相对维数为 $d$ 的光滑态射，其任意基变换仍光滑，相对维数为 $d$。 

  + 若 $f: X -> Y$ 光滑、相对维数为 $d$，$g: Y -> Z$ 光滑、相对维数为 $e$，则 $g compose f: X -> Z$ 光滑，相对维数为 $d+e$。 
]
#proof[
  这些性质都来自分解 $X -> AA^d_Y -> Y$，其中 $X -> AA^d_Y$ 平展。 
]
