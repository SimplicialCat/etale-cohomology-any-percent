#import "void-import.typ": *
== $cAb(X_et)$ 作为 Abel 范畴 <sect-ab-x-et-as-abelian-cat>

/*
#date[第 6 讲，2025/10/29
  #set align(left)
  第一份习题已在 Web Learning 上发布。请阅读说明，并记住：这份习题的批改标准与审稿相同。 

  今天我们来讨论： 
  - $cAb(X_et)$； 
  - 函子性； 
  - 茎； 
  - 域的平展景。 
]

设 $X$ 是概形。于是 $X$ 对应一个平展景 $X_et$，在其上有集合、交换群的预层/层构成的范畴： 
$
  iota: cSh(X_et) arrow.r.hook cPSh(X_et), cAb(X_et) arrow.r.hook cPAb(X_et)
$
上一讲我们证明了遗忘函子 $iota$ 有右伴随 $cal(G) |-> cal(G)^\#$，其构造大致如下： 
*/

正如上一节开头所说，接下来几节我们会陆续介绍获得平展层的几种不同方法。本节讲的是其中的第二种：利用 $cAb(X_et)$ 的 Abel 范畴结构。 

因此，要说明 $cAb(X_et)$ 是一个性质良好的 Abel 范畴，我们需要建立下面这些构造与结果： 

- 层化； 
- $cAb(X_et)$ 是 Abel 范畴（即可以定义核、余核与像）； 
- $cAb(X_et)$ 有足够多的内射对象。 

我们的第一个目标是层化。 

#construction(name: <constr-zeroth-cech-cohom>)[
  对 $Et_X$ 中任意平展覆盖 $cal(U) = {U_i -> U}_i$ 以及任意 $cal(G) in cPSh(X_et)$，把 $cal(G)$ 关于 $cal(U)$ 的*零次 Čech 上同调*定义为如下等化子，并记作 $caron(H)^0 (cal(U), cal(G))$： 
  $
    caron(H)^0 (cal(U), cal(G)) -> product_i cal(G)(U_i) arrows.rr product_(i,j) cal(G)(U_i times_U U_j)
  $
  换言之，$caron(H)^0 (cal(U), cal(G))$ 的元素是一族截面 ${s_i in cal(G)(U_i)}$，要求它们在 ${U_i}$ 的交（即纤维积）上彼此一致。 

  给定平展覆盖 $cal(U) = {U_i -> U}_(i in I)$，所谓 $cal(U)$ 的加细 (refinement)，指的是一个平展覆盖 $cal(V) = {V_j -> U}_(j in J)$，连同指标映射 $lambda: J -> I$，以及对每个 $j in J$ 的分解 $V_j -> U_(lambda(j)) -> U$。给定 $cal(U)$ 的一个加细 $cal(V)$，有自然态射 $product_i cal(G)(U_i) -> product_j cal(G)(V_j), (s_i) |-> (s_(lambda(j))|_(V_j))_j$，以及类似的态射 $product_(i,i') cal(G)(U_i times_U U_(i')) -> product_(j,j') cal(G)(V_j times_V V_(j'))$。由此诱导出自然态射： 
  $
    caron(H)^0 (cal(U), cal(G)) -> caron(H)^0 (cal(V), cal(G))
  $
  #lemma[
    考虑下面这个态射：
    $
      caron(H)^0 (cal(U), cal(G)) -> caron(H)^0 (cal(V), cal(G))
    $
    由 $cal(U)$ 到 $cal(V)$ 的任意两个不同加细所诱导的态射都相同。 
  ]
  #proof[
    给定 $cal(V)$ 对 $cal(U)$ 的两个加细，其指标映射为 $lambda, lambda': J -> I$。我们需要证明：对每个 $s = (s_i) in caron(H)^0 (cal(U), cal(G))$，都有 
    $
      s_(lambda(j))|_(V_j) = s_(lambda'(j))|_(V_j)
    $
    对每个 $j$ 都成立。然而，由于 $s in caron(H)^0 (cal(U), cal(G))$， 
    $
      s_(lambda(j))|_(U_(lambda(j)) times_U U_(lambda'(j))) = s_(lambda'(j))|_(U_(lambda(j)) times_U U_(lambda'(j)))
    $
    另一方面，这两个加细给出了 $V_j -> U$ 在 $Et_X$ 中的两个分解：$V_j -> U_(lambda(j)) -> U$ 与 $V_j -> U_(lambda'(j)) -> U$。于是取纤维积，便得到分解 $V_j -> U_(lambda(j)) times_U U_(lambda'(j)) -> U$。再把上面的等式限制到 $V_j$，便完成证明。 
  ]
  
  定义 $cal(G)$ 在 $U$ 上的*零次 Čech 上同调*为正向极限： 
  $
    caron(H)^0 (U, cal(G)) = dirlim_(cal(U)) caron(H)^0 (cal(U), cal(G))
  $
  这里极限取遍由 $U$ 的所有平展覆盖 $cal(U)$ 构成的正向集，其中 $cal(U) <= cal(V)$ 当且仅当存在从 $cal(U)$ 到 $cal(V)$ 的加细。过渡映射由前面的加细给出；由于这些过渡映射不依赖具体的加细，故良定义。 

  #remark(name: <set-categorical-subtleties>)[
    这个定义里至少有两处微妙之处：#footnote[这两处困难我起初都没有意识到。范畴论那一处，是我在写下一节关于茎的内容时想到的：在一些 AI 的协助下，我意识到两个加细未必能被等化。后来我发现 @cite-lei-fu 里已经记录了这一点。集合论那一处则来自 Irisu：当时我在一次小组讨论里提到了范畴论这处微妙之处，Irisu 便告诉了我集合论那一处。] 

    - 范畴论上的微妙之处： 
    
      如果天真地把 $caron(H)^0 (U, cal(G)) = colim_(cal(U)) caron(H)^0 (cal(U), cal(G))$ 当作定义，其中余极限取遍以 $U$ 的平展覆盖为对象、以加细为态射的范畴，那么这个余极限不是滤过的。原因在于：给定同一对覆盖的两个加细，未必能再用更细的加细把它们等化。 

      我们最终要靠 $caron(H)^0 (U, cal(G))$ 是作为滤余极限定义的 这一点，来证明层化与有限极限交换、从而是正合的。因此，若当初把加细当作指标范畴里的态射来定义 $caron(H)^0$，那时还必须证明这个任意的余极限其实是正向极限，为此要重述那条引理：同一对覆盖之间的两个不同加细诱导相同的过渡态射。换言之，前面那条引理是这套理论中不可缺少的一环。 

      所以更好的做法是：就像这里一样，把 $caron(H)^0 (U, cal(G))$ 定义为平展覆盖上的正向极限，其中的态射是_作为性质_的加细，而不是_作为结构_的加细。 

    - 集合论上的微妙之处： 

      假定我们所处的 Grothendieck 宇宙是 $cal(W)$，其中#footnote[这里用 $cal(W)$ 而不用习惯的 $cal(U)$，是因为这个语境里 $cal(U)$ 已经用来表示平展覆盖了。]我们的集合都是 $cal(W)$-集合，概形都是 $cal(W)$-概形，诸如此类。那么一般来说，$U$ 的所有平展覆盖构成的集合（当然是由 $cal(W)$-集合作指标、用 $cal(W)$-概形给出的）与 $cal(W)$ 基数相同，因此不是 $cal(W)$-集合。于是先验地就有个顾虑：上面的正向极限可能不作为 $cal(W)$-集合存在。 

      这个集合论问题可以这样解决：考虑平展覆盖的如下子族 $cal(S)$： 

      - 平展覆盖 $cal(U) = {U_i -> U}$，其中每个 $U_i$ 都仿射、像落在 $U$ 的某个仿射开集里，并且 $cal(U)$ 中任意两个态射都不同构。 

      先取足够小的仿射开集、再去掉重复项之后，就容易看出：$U$ 的每个平展覆盖都能被 $cal(S)$ 中的某个覆盖加细。另一方面，$U$ 的仿射开集构成一个 $cal(W)$-集合；而对每个仿射开集 $Spec(A) subset U$，任意平展 $A$-代数都是 $A$ 上有限型的，因此同构于某个 $A[x_1, dots.c, x_k]$ 的商。这样的同构类至多有 $max(aleph_0, abs(A))$ 个，从而构成一个 $cal(W)$-集合。换言之，$cal(S)$ 中每个覆盖的态射都取自某个 $cal(W)$-集合。因此 $cal(S)$ 是 $cal(W)$-集合。 

      既然 $U$ 的每个平展覆盖都能被 $cal(S)$ 中的覆盖加细，正向极限 
      $
        dirlim_(cal(U)) caron(H)^0 (cal(U), cal(G)) = dirlim_(cal(U) in cal(S)) caron(H)^0 (cal(U), cal(G))
      $
      就作为 $cal(W)$-集合存在。 
  ]
]

#definition[
  若对任意平展覆盖 $cal(U) = {U_i -> U}$，映射 
  $
    cal(G)(U) -> caron(H)^0 (cal(U), cal(G))
  $
  都是单射，则称预层 $cal(G)$ 是*分离的*。 
  
  可以看出 $cal(G)^+$ 分离；且若 $cal(G)$ 分离，则 $cal(G) arrow.r.hook cal(G)^+$，此时 $cal(G)^+$ 已经是层。 
]

#lemma[
  *Grothendieck 加号构造*： 
  $
    (-)^+: cPSh(X_et) -> cPSh(X_et), cal(G) |-> (cal(G)^+: Z |-> caron(H)^0 (Z, cal(G)))
  $
  满足： 

  + 对任意 $cal(G) in cPSh(X_et)$，$cal(G)^+$ 分离； 

  + 对任意分离的 $cal(G) in cPSh(X_et)$，$cal(G)^+$ 是层。 
]
#proof[
  (1) 我们要证：对任意平展覆盖 $cal(U) = {U_i -> U}_(i in I)$ 与任意 $s, t in cal(G)^+ (U) = caron(H)^0 (U, cal(G))$，若 $s|_(U_i) = t|_(U_i), forall i in I$，则 $s = t$。 

  由构造，$s$ 来自 $U$ 的某个平展覆盖 $cal(V)$ 对应的 $caron(H)^0 (cal(V), cal(G))$。取 $s,t$ 各自对应的覆盖和 $cal(U)$ 三者的一个共同加细，便可假设 $s, t$ 都来自 $caron(H)^0 (cal(V), cal(G))$，其中 $cal(V) = {V_j -> U}_(j in J)$ 加细 $cal(U)$。也就是说，$s = (s_j)$，其中 $s_j in cal(G) (V_j)$，$t$ 同理。 

  我们把条件 $s|_(U_i) = t|_(U_i)$ 按定义展开。这些截面在正向极限中来自 $caron(H)^0 (cal(V) times_U U_i, cal(G))$，故存在 $cal(V) times_U U_i$ 的一个加细 $cal(W)_i = {W_(i,k) -> U_i}_(k in K_i)$，连同指标映射 $lambda_i: K_i -> J$。于是条件 $s|_(U_i) = t|_(U_i)$ 展开为： 
  $
    s_(lambda_i (k))|_(W_(i,k)) = t_(lambda_i (k))|_(W_(i,k)) in cal(G)(W_(i,k)), forall k in K_i
  $
  令 $K = union.sq.big_(i in I) K_i$。则 $cal(W) = {W_(i,k) -> U_i -> U}_(k in K)$ 加细 $cal(V)$（指标映射为 $lambda = union.sq.big_(i in I) lambda_i : K -> J$）。由上面展开的条件，从 $cal(V)$ 过渡到 $cal(W)$ 即得 $s = t in caron(H)^0 (U, cal(G))$。 

  (2) 注意存在自然映射 $cal(G)(U) -> cal(G)^+ (U)$，从而有自然的预层态射： 
  $
    theta: cal(G) -> cal(G)^+
  $
  $cal(G)$ 分离，意味着 $theta$ 是单射，即在截面上为单射。 
  
  $cal(G)^+$ 的分离性已在 (1) 中证得，故只需证 $cal(G)^+$ 的截面可以粘接。 

  设 $cal(U) = {U_i -> U}$ 是平展覆盖，${s_i in cal(G)^+ (U_i)}$ 是一族在 $cal(G)^+$ 中彼此相容的截面。 
  
  按定义，对每个 $i$ 都存在平展覆盖 $cal(U)_i = {U_(i,j) -> U_i}$，使得 $s_i$ 由一族对 $cal(G)$ 相容的截面 ${s_(i,j) in cal(G)(U_(i,j))}_j$ 给出。 

  我们断言：族 ${s_(i,j) in cal(G)(U_(i,j))}_(i,j)$ 定义了 $caron(H)^0 (cal(U)', cal(G))$ 的一个元素，其中 $cal(U)' = {U_(i,j) -> U_i -> U}_(i,j)$ 是拼合起来的平展覆盖。 

  为此要证 $s_(i,j)$ 与 $s_(i',j')$ 在 $U_(i,j) times_U U_(i',j')$ 上相容。由于 $theta$ 是单射，只需证明：在 $cal(G)^+ (U_(i,j) times_U U_(i',j'))$ 中，$theta(s_(i,j)) = theta(s_(i',j'))$。 

  然而按假设，限制到 $cal(G)^+ (U_i times_U U_(i'))$ 上有 $s_i = s_(i')$。把定义展开，便有 $theta(s_(i,j)) = s_i|_(U_(i,j))$，对带撇的 $s_(i',j')$ 同理。至此相容性证完。于是存在良定义的截面 $s in cal(G)^+ (U)$，使得 $s|_(U_(i,j)) = s_(i,j) = s_i|_(U_(i,j))$。由分离性，$s|_(U_i) = s_i$，粘接性得证。 
]

由上面的引理，对任意预层 $cal(G)$，$(cal(G)^+)^+$ 总是层。于是可以定义层化。

#definition(name: <defn-sheafification>)[
  *层化*函子定义为： 
  $
    (-)^\#: cPSh(X_et) -> cSh(X_et), cPAb(X_et) -> cAb(X_et), cal(G) |-> cal(G)^\# := (cal(G)^+)^+
  $
]

#proposition[
  // 遗忘函子 $iota: cSh(X_et) -> cPSh(X_et)$ 有左伴随 $(-)^\#$，称为*层化*。 
  层化 $(-)^\#$ 是遗忘函子 $iota: cSh(X_et) -> cPSh(X_et)$ 的左伴随。 
]
#proof[
  $cSh(X_et)$ 是 $cPSh(X_et)$ 的满子范畴。因此只需证明自然映射 $cal(F) -> cal(F)^\#$ 诱导出自然同构： 
  $
    Hom_(cPSh) (cal(F)^\#, cal(G)) -> Hom_(cPSh) (cal(F), cal(G))
  $
  对任意的_层_ $cal(G) in cSh(X_et)$ 成立。 

  由于 $(-)^\#$ 就是 $(-)^+$ 作用两次，只需证明： 
  $
    Hom_(cPSh) (cal(F)^+, cal(G)) -> Hom_(cPSh) (cal(F), cal(G))
  $
  即由 $theta: cal(F) -> cal(F)^+$ 诱导的态射是同构。 

  先证单射性：给定态射 $f, g: cal(F)^+ -> cal(G)$，若 $f compose theta = g compose theta$，则对任意由 ${s_i in cal(F)(U_i)}$ 表示的 $s in cal(F)^+ (U)$， 
  $
    f(s)|_(U_i) = f(s|_(U_i)) = f(theta(s_i)) = g(theta(s_i)) = g(s)|_(U_i)
  $
  于是由 $cal(G)$ 的层条件，$f(s) = g(s)$。因此 $f = g$。 

  再证满射性，即任意态射 $f': cal(F) -> cal(G)$ 都穿过 $theta$ 分解。事实上，给定由 ${s_i in cal(F)(U_i)}$ 表示的任意 $s in cal(F)^+ (U)$，截面 ${f'(s_i) in cal(G)(U_i)}$ 在每个 $U_i times_U U_j$ 上都相容，这是因为 $f'$ 与限制相容，而 ${s_i}$ 彼此相容。于是 ${f'(s_i)}_i$ 粘接成截面 $t in cal(G)(U)$。令 $f(s) = t$。容易验证 $f$ 是层之间的态射，且 $f' = f compose theta$。 
]

#let Fun = math.op[Fun]
#lemma[
  对任意范畴 $cal(C)$，$Fun(cal(C), cAb)$ 是 Abel 范畴，且有足够多的内射对象；其中的核、余核、像以及极限、余极限都逐点取。 
]
#proof[
  这个论证是纯形式的。 
]

#corollary[
  $cPAb(X_et)$ 是 Abel 范畴，有足够多的内射对象，其核、余核、像逐截面取。极限与余极限也逐截面取。 
]
#proof[
  在上一引理中取 $cal(C) = Et_X^opp$。 
]

#lemma[
  $(-)^+, (-)^\#$ 与有限极限交换，也就是说，在交换群预层的范畴上，它们是左正合的。 
]
#proof[
  由于 $(-)^\#$ 就是 $(-)^+$ 作用两次，只需证明 $(-)^+$ 与有限极限交换。 

  不过，我们来看构造 $(-)^+$ 的两个步骤。由于 $cPSh(X_et)$ 与 $cPAb(X_et)$ 中的极限、余极限都逐截面取，只需固定在某个 $U in Et_X$ 上考虑。此时： 
  
  - $caron(H)^0 (cal(U), cal(F)) = ker(product_i cal(F)(U_i) -> product_(i,j) cal(F)(U_i times_U U_j))$ 是等化子，从而是极限。它当然与任何极限交换。 

  - $cal(F)^+ (U) = dirlim_(cal(U)) caron(H)^0 (cal(U), cal(F))$ 是滤余极限，它与有限极限交换。 
]

#example(name: <detection-and-const-sheaf>)[
  借助层化，我们可以构造更多平展层： 

  + 对 $V in X_et$，用 $U |-> oplus.big_(Hom_X (U, V)) ZZ$ 定义 $ul(ZZ)_(!,V,0) in cPAb(X_et)$。于是对 $cal(G) in cPAb(X_et)$ 有同构： 
    $
      Hom_(cPAb) (ul(ZZ)_(!,V,0), cal(G)) overset(->, tilde) cal(G)(V), (f: ZZ_V -> cal(G)) |-> f_V (1_(id_V))
    $
    于是层化 $ul(ZZ)_(!,V) = ul(ZZ)_(!,V,0)^\# in cAb(X_et)$ 会满足：对 $cal(F) in cAb(X_et)$， 
    $
      Hom_(cAb(X_et)) (ul(ZZ)_(!,V), cal(F)) = Hom_(cPAb(X_et)) (ul(ZZ)_(!,V,0), cal(F)) = cal(F)(V)
    $
    
    换言之，从 $ul(ZZ)_(!,V)$ 出发的态射可以探测 $V$ 上的截面。这个构造在一般理论里小有用处。 

  + 对任意交换群 $M$，定义 $X$ 上与 $M$ 相伴的*常值层* $ul(M)_X$ 为如下预层的层化：该预层把每个非空的 $U$ 都送到 $M$。 

    /*
    #lemma[
      对每个连通的 $U in Et_X$，自然有 $ul(M)_X (U) cong M$。作为推论，对那些能写成其连通分支的不交并的 $U in Et_X$#footnote[在非 Noether 情形下这不自动成立。]，有 
      $
        ul(M)_X (U) cong product_(pi_0 (U)) M
      $
      这正是层条件给出的。 
    ]
    #proof[
      由于常值预层 $ul(M)_(X,0): U |-> M$（对 $U != emptyset$）本身已经分离，故 $ul(M)_X = ul(M)_(X,0)^\# = ul(M)_(X,0)^+$。 

      给定任意平展覆盖 $cal(U) = {f_i: U_i -> U}_i$，我们需要计算 $caron(H)^0 (cal(U), ul(M)_(X,0))$： 
      $
        caron(H)^0 (cal(U), ul(M)_(X,0)) = ker(product_i ul(M)_(X,0) (U_i) -> product_(i,j) ul(M)_(X,0) (U_i times_U U_j))
      $
      它由那些 $(s_i) in product_i M$ 组成，其中只要 $U_i times_U U_j$ 非空就有 $s_i = s_j$。特别地，只要 $V_i ∩ V_j$ 非空就有 $s_i = s_j$，这里 $V_i = f_i (U_i)$ 是 $U$ 的开集。 

      对每个固定的 $i$，令 $I_i = {j in I: exists k_0, k_1, dots.c, k_n in I, k_0 = i, k_n = j, V_(k_m) ∩ V_(k_(m+1)) != emptyset}$。现在定义： 
      $
        W_i = union.big_(j in I_i) V_j
      $
      则 $W_i$ 是 $U$ 的开集。此外 $W_i^c$ 也是 $U$ 的开集。事实上，对任意 $x in W_i^c$，由联合满射性存在 $k in I$ 使 $x in V_k$。若 $V_k$ 与 $W_i$ 相交，则它必与某个 $j in I_i$ 的 $V_j$ 相交。于是把 $k$ 接在 $I_i$ 定义中的链 $j$ 之后，便知 $k in I_i$，从而 $x in V_k subset W_i$，矛盾。故 $V_k subset W_i^c$。既然 $W_i$ 是 $U$ 的非空闭开子集，由连通性 $W_i = U$。于是对每个 $k in I$，$V_k$ 都与 $W_i$ 相交，从而与某个 $j in I_i$ 的 $V_j$ 相交。故 $k in I_i$ 亦然。于是 $I_i = I$；换言之，每个 $j in I$ 都可经由链 $k_0, dots.c, k_n$ 从 $i$ 到达，其中每步 $V_(k_m) ∩ V_(k_(m+1)) != emptyset$。因此 $s_i = s_j, forall j in I$。 

      换言之， 
      $
        ul(M)_X (U) = dirlim_(cal(U)) caron(H)^0 (cal(U), ul(M)_(X,0)) = dirlim_(cal(U)) M = M
      $
    ]*/

    #lemma[
      对任意 $U in Et_X$，有自然同构： 
      $
        ul(M)_X (U) cong C(U; M_#[disc]) = {#[局部常值函数] f: U -> M}
      $
      在此同构下，若层态射 $phi: ul(M)_X -> cal(G)$ 由预层态射 $phi_0: ul(M)_(X,0) -> cal(G)$ 诱导，即由一族相容的态射 ${M -> cal(G)(U)}_(U in Et_X)$ 诱导，则 $phi$ 由下式给出： 
      $
        ul(M)_X (U) = C(U; M_#[disc]) &-> cal(G)(U) \
        f &|-> (phi_0 (x) in cal(G)(f^(-1)(x))) in cal(G)(U) = cal(G)(union.sq.big_(x in M) f^(-1)(x)) = product_(x in M) cal(G)(f^(-1) (x))
      $
    ]
    #proof[
      由于 $ul(M)_(X,0)$ 是分离预层，$ul(M)_X = ul(M)_(X,0)^+$，也就是说加号构造只需用一次。 

      对平展覆盖 $cal(U) = {f_i: U_i -> U}$， 
      $
        caron(H)^0 (cal(U), ul(M)_(X,0)) = ker(product_i M -> product_(i,j) ul(M)_(X,0) (U_i times_U U_j))
      $
      其中当 $f_i (U_i) ∩ f_j (U_j) = emptyset$ 时 $ul(M)_(X,0) (U_i times_U U_j) = 0$，否则为 $M$。于是 
      $
        caron(H)^0 (cal(U), ul(M)_(X,0)) = {(m_i) in M^I : m_i = m_j #[若] f_i (U_i) ∩ f_j (U_j) != emptyset} subset M^I
      $
      给定元素 $mu = (m_i) in caron(H)^0 (cal(U), ul(M)_(X,0))$，可以对每个 $x in M$ 定义集合 
      $
        U_(mu,x) = union.big_(i in I \ m_i = x) f_i (U_i) subset U
      $
      对每个 $x$，相应的集合都是开集；不同 $x$ 对应的集合互不相交，因为 $m_i != m_j$ 推出 $f_i (U_i) ∩ f_j (U_j) = emptyset$。又因 $cal(U)$ 联合满射，它们覆盖 $U$。换言之，我们得到了由闭开子集给出的划分 $U = union.sq.big_(x in M) U_(mu,x)$。于是定义 
      $
        f_mu = sum_(x in M) x bold(1)_(U_(mu,x)) in C(U; M_#[disc])
      $
      这就给出自然态射 $caron(H)^0 (cal(U), ul(M)_(X,0)) -> C(U; M_#[disc])$，容易看出它与正向系统内的态射相容。于是有自然态射： 
      $
        ul(M)_X(U) = dirlim_(cal(U)) caron(H)^0 (cal(U), ul(M)_(X,0)) -> C(U; M_#[disc])
      $
      这个态射是满射：给定任意 $f in C(U; ul(M)_#[disc])$，取 Zariski 覆盖 $cal(U)_f = {f^(-1)(x) -> U}_(x in M)$，则 $(x)_x in caron(H)^0 (cal(U)_f, ul(M)_(X,0))$ 在这个态射下被送到 $f$。它也是单射：若 $mu = (m_i)_(i in I) in caron(H)^0 (cal(U), ul(M)_(X,0))$ 被送到 $0$，就说明对所有 $0 != x in M$ 都有 $U_(mu,x) = emptyset$，即每个 $m_i = 0$。至此证毕。关于诱导态射的结论，只是把层化的伴随同构的定义展开而已。 
    ]
]

#theorem(name: <ab-x-et-the-abelian-cat>)[
  // + $cPAb(X_et)$ 是 Abel 范畴，且有足够多的内射对象。$cal(F) -> cal(G)$ 是单态射/满态射（即单射/满射）$<==>$ 对每个 $U in X_et$，$cal(F)(U) -> cal(G)(U)$ 都是单射/满射。正合列、核、余核等等也一样。 

  + $cAb(X_et)$ 是 Abel 范畴。更确切地说，对 $f: cal(F) -> cal(G)$，其核、余核与像可以这样计算： 
    $
      ker(f) = (U |-> ker(f_U\: cal(F)(U) -> cal(G)(U))) \

      coker(f) = (U |-> coker(f_U\: cal(F)(U) -> cal(G)(U)))^\# \

      im(f) cong op("coim")(f) = 
      coker(ker(f)) = (U |-> im(f_U\: cal(F)(U) -> cal(G)(U)))^\#
    $
    换言之，核就是预层意义下的核，而余核与像则是预层余核、预层像的层化。 

  + 对 $cAb(X_et)$ 中的 $f: cal(F) -> cal(G)$，$f$ 是单态射（单射）$<==>$ 对每个 $U in X_et$，$f_U: cal(F)(U) -> cal(G)(U)$ 都是单射。 
  
    另一方面，$f$ 是满态射（满射）$<==>$ 对任意 $U in X_et, s in cal(G)(U)$，都存在平展覆盖 ${U_i -> U}$，使得对所有 $i$ 有 $s|_(U_i) in im(f_(U_i))$。 

  + 在 $cAb(X_et)$ 中计算极限与余极限： 
    $
      lim_(i in I) cal(F)_i = lim_(i in I) iota(cal(F)_i) , colim_(i in I) cal(F)_i = (colim_(i in I) iota(cal(F)_i))^\#
    $
    也就是说，层的极限就是它们作为预层的极限，而余极限是预层余极限的层化。 

  + $cAb(X_et)$ 有足够多的内射对象。 

  0. $(-)^\#: cPAb(X_et) -> cAb(X_et)$，即层化函子，是正合的。 

//   #remark[
//     所有这些 (1)-(4) 对任意景 $cal(C)$ 仍然成立，而 (3) 对 $cSh(X_et), cSh(X_et)$ 成立。 
// ]
]
#proof[
  (0) 假设已证 (1)，即 $cAb(X_et)$ 是 Abel 范畴。那么由已证的结果，层化与有限极限交换（从而左正合），又是左伴随（从而右正合），故它正合。 

  (1) 关于核：遗忘函子 $iota: cAb(X_et) -> cPAb(X_et)$ 是右伴随，保持所有极限。特别地，它保持核，所以 $cPAb$ 中的核就是 $cAb$ 中的核。 

  关于余核：设 $cal(F) ->^f cal(G) -> cal(P)$ 是 $cPAb$ 中的余核，要证 $cal(P)^\#$ 是 $cAb$ 中的余核。事实上，由于复合 $cal(F) ->^f cal(G) -> cal(P)$ 已是零，$cal(F) ->^f cal(G) -> cal(P)^\#$ 也是零。对任意使 $cal(F) ->^f cal(G) ->^g cal(H)$ 复合为零的 $cal(H) in cAb(X_et)$，由预层余核的泛性质，$g$ 分解为： 
  $
    cal(G) -> cal(P) -> cal(H)
  $
  然而 $cal(H)$ 是层，由层化的伴随关系，$g$ 进一步分解为： 
  $
    cal(G) -> cal(P) -> cal(P)^\# -> cal(H)
  $
  从而穿过 $cal(G) -> cal(P)^\#$ 分解。因此 $cal(G) -> cal(P)^\#$ 是 $f$ 在 $cAb(X_et)$ 中的余核。（注意这个论证同样是纯范畴论的、抽象的。） 

  为证明 $cAb(X_et)$ 是 Abel 范畴、且像由上述公式给出，剩下只需证明：在 $cAb(X_et)$ 中，核的余核等于余核的核。我们用下标 $cPAb$ 与 $cAb$ 区分预层余核与层余核，对核则不区分（因为预层与层的核相同）。于是： 
  $
    coker_(cAb)(ker(f)) &= coker_(cPAb) (ker(f))^\# \
    &= ker(coker_(cPAb)(f))^\# #[因为 $cPAb(X_et) $ 是 Abel 范畴] \
    &= ker(coker_(cPAb)(f)^\#) #[因为 $(-)^\#$ 与有限极限交换] \
    &= ker(coker_(cAb)(f))
  $
  像的公式随即由“核的余核”得到。 

  (2) 由 (1) 中的公式得到。 

  (3) 由于 $iota: cAb(X_et) -> cPAb(X_et)$ 是右伴随，它与所有极限交换，故 $cAb$ 中的极限可以在 $cPAb$ 中计算。至于余极限，我们用一个类似的抽象论证，说明层余核就是预层余核的层化。 

  给定任意图表 $cal(F): I -> cAb(X_et)$ 与任意从图表 $cal(F)$ 到对象 $cal(G) in cAb(X_et)$ 的态射，把图表经 $iota$ 送进 $cPAb(X_et)$，便得到唯一的态射 $colim_(i in I) iota(cal(F)_i) -> iota(cal(G))$。由伴随性，存在唯一的态射 $(colim_(i in I) iota(cal(F)_i))^\# -> cal(G)$。于是按定义， 
  $
    (colim_(i in I) iota(cal(F)_i))^\# = colim_(i in I) cal(F)_i
  $

  (4) 
  #remark[
    要证明平展层构成的范畴有足够多的内射对象，至少有两条路： 

    + 用 @cite-grothendieck-tohoku 抽象地得到内射对象； 

    + 用 Godement 消解。 

    Godement 消解，也就是第二条路，好处是它给出显式的构造，而且是函子性的。但它需要先定义平展层在几何点处的茎 (stalk)，因此我们把它留到后面某一节再介绍。 
    
    另一方面，第一条路虽然抽象，但它事实上也是函子性的构造，而且好处是不只对平展景有效，对 fppf、fpqc 与晶体#footnote[…管它是什么意思。]景这类没有足够多点的景同样有效。我们现在先走第一条路，等引入茎之后再讨论第二条路。 
  ]

  下面的定理来自 @cite-grothendieck-tohoku：
  #theorem[
    设 Abel 范畴 $cal(A)$ 满足以下条件： 

    + (Ab5) 条件：$cal(A)$ 有任意余积，且滤余极限正合。 

    + $cal(A)$ 有生成元 (generator) $G$，即存在对象 $G in cal(A)$，使得 $Hom(G, -): cal(A) -> cAb$ 忠实。 

    则 $cal(A)$ 有足够多的内射对象；事实上，它还有函子性的内射消解。
  ]

  于是我们需要说明 $cAb(X_et)$ 满足 (Ab5) 且有生成元。 

  (Ab5)： 
  #proof[
    层的任意直和可以逐截面地作出。此外 $cPAb(X_et)$ 满足 (Ab5)：按截面逐项验证即可，由此可知 (Ab5) 对 $cAb$ 也成立。 

    设 ${0 -> cal(F)_i -> cal(G)_i -> cal(H)_i -> 0}_i$ 是 $cAb(X_et)$ 中由正合列构成的正向系统。由于函子 $iota$ 左正合，我们有左正合列： 
    $
      0 -> iota(cal(F)_i) -> iota(cal(G)_i) -> iota(cal(H)_i) 
    $
    在 $cPAb(X_et)$ 中。取余核，可以将它延长为四项正合列： 
    $
      0 -> iota(cal(F)_i) -> iota(cal(G)_i) -> iota(cal(H)_i) -> cal(R)_i -> 0
    $
    接着对这个序列层化。由于层化函子 $(-)^\#$ 正合，得到正合列： 
    $
      0 -> cal(F)_i -> cal(G)_i -> cal(H)_i -> cal(R)_i^\# ->  0
    $
    于是对每个 $i$ 都有 $cal(R)_i^\# = 0$。 

    接下来，对序列 $0 -> iota(cal(F)_i) -> iota(cal(G)_i) -> iota(cal(H)_i) -> cal(R)_i -> 0$ 取正向余极限，并利用 $cPAb(X_et)$ 的 (Ab5)，得到正合列： 
    $
      0 -> dircolim_i iota(cal(F)_i) -> dircolim_i iota(cal(G)_i) -> dircolim_i iota(cal(H)_i) -> dircolim_i cal(R)_i -> 0
    $
    再取层化（层化正合），并利用等式 $dircolim_i cal(F)_i = (dircolim_i iota(cal(F)_i))^\#$，得到正合列： 
    $
      0 -> dircolim_i cal(F)_i -> dircolim_i cal(G)_i -> dircolim_i cal(H)_i -> (dircolim_i cal(R)_i)^\# -> 0
    $
    由于层化是左伴随，它保持所有余极限，故 $(dircolim_i cal(R)_i)^\# = dircolim_i cal(R)_i^\# = 0$（因为每个 $cal(R)_i^\# = 0$）。于是得到正合列 $0 -> dircolim_i cal(F)_i -> dircolim_i cal(G)_i -> dircolim_i cal(H)_i -> 0$。 
    #suppress-qed
  ]

  生成元的存在性： 
  #proof[
    我们希望取生成元 $G = oplus.big_(U in Et_X) ul(ZZ)_(!,U)$。但受集合论困难所限，这行不通： 

    - 谈论集合、概形等等时，我们总固定一个背景 Grothendieck 宇宙 $cal(U)$，实际谈论的是 $cal(U)$-集合与 $cal(U)$-概形（也就是涉及的结构都是 $cal(U)$ 中集合的概形）。因此直和必须以 $cal(U)$-集合为指标；但一般而言，$Et_X$ 即 $X$ 上平展的 $cal(U)$-概形构成的范畴，可以包含这样的概形，即 $X$ 上的平展概形以任意 $cal(U)$-集合为指标的不交并；这个范畴的基数与 $cal(U)$ 相同。 

    于是改用平展拓扑在 $X$ 上的一组基。设 $X$ 被仿射开集 ${Spec(A_i)}_(i in I)$ 覆盖，其中 $I$ 是 $cal(U)$-集合，每个 $A_i$ 是 $cal(U)$-环。令 $cal(S)_i$ 为平展 $A_i$-代数的同构类构成的集合。由于平展 $A_i$-代数在 $A_i$ 上有限型，它们都同构于某个 $A_i [x_1, dots.c, x_k]$ 的商（$k$ 适当选取），因此这样的同构类至多有 $max(aleph_0, abs(A_i))$ 个。于是每个 $cal(S)_i$ 都是 $cal(U)$-集合，从而不交并 $cal(S) = union.sq.big_(i in I) cal(S)_i$ 也是 $cal(U)$-集合。 

    我们断言：$cAb(X_et)$ 中的态射 $f: cal(F) -> cal(G)$，若对每个 $i$ 与每个 $B_i in cal(S)_i$，它在平展开集 $Spec(B_i) -> Spec(A_i) -> X$ 的截面上都为零，则 $f$ 为零。事实上，对任意 $U in Et_X$，可以用仿射开集覆盖 $U$，使它们在 $X$ 中的像落在某个 $Spec(A_i)$ 内，即 $U = union.big_(i,j) Spec(C_(i,j))$，其中 $C_(i,j)$ 是 $cal(S)_i$ 中某个同构类的代表（即同构于该同构类中的某个环）。由于它在每个 $C_(i,j)$ 的截面上为零，由层条件，$f$ 在 $U$ 的截面上为零。因此 $f = 0$。 

    换言之，取下面这个以 $cal(U)$-集合 $cal(S)$ 为指标的直和： 
    $
      G = oplus.big_(B_i in cal(S)) ul(ZZ)_(!,Spec(B_i))
    $
    则 $G$ 使 $Hom(G, -): cAb(X_et) -> cAb$ 忠实，因此 $G$ 是生成元。 

    #suppress-qed
  ]

  借助 @cite-grothendieck-tohoku，便知 $cAb(X_et)$ 有足够多的内射对象。 

  // (2) 也可以直接验证 $ker(f), coker(f)$ 由上述公式给出。要证明 $cAb(X_et)$ 是 Abel 范畴，只需证明： 
  // $
  //   coker(ker(f) -> cal(F)) = op("coim")(f) -> im(f) = ker(cal(G) -> coker(f))
  // $
  // 是同构。也就是 
  // $
  //   (im^(cPSh(X_et)) (f))^\# -> ker(cal(G) -> coker(f))
  // $
  // 是同构。考虑 $cPAb(X_et)$ 中的图表： 
  // // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFs0LDAsIjAiXSxbMSwwLCJpbV4oY1BTaCkoZikiXSxbMiwwLCJjYWwoRykiXSxbMywwLCJjb2tlcl4oY1BTaCkgKGYpIl0sWzAsMSwiMCJdLFsxLDEsIihpbV4oY1BTaCkoZikpXlxcIyJdLFsyLDEsImNhbChHKV5cXCMiXSxbMywxLCIoY29rZXJeKGNQU2gpIChmKSleXFwjIl0sWzQsMSwiMCJdLFswLDJdLFsyLDNdLFszLDRdLFs0LDFdLFs1LDZdLFs2LDddLFs3LDhdLFs4LDldLFsyLDYsIiIsMSx7InN0eWxlIjp7InRhaWwiOnsibmFtZSI6Imhvb2siLCJzaWRlIjoiYm90dG9tIn19fV0sWzMsNywidGlsZGUiLDFdLFs0LDhdXQ==
  // #context align(center, diagram({
  //   node((-2, -1), [$0$])
  //   node((2, -1), [$0$])
  //   node((-1, -1), [$im^(cPSh)(f)$])
  //   node((0, -1), [$cal(G)$])
  //   node((1, -1), [$coker^(cPSh) (f)$])
  //   node((-2, 0), [$0$])
  //   node((-1, 0), [$(im^(cPSh)(f))^\#$])
  //   node((0, 0), [$cal(G)^\#$])
  //   node((1, 0), [$(coker^(cPSh) (f))^\#$])
  //   node((2, 0), [$0$])
  //   edge((-2, -1), (-1, -1), "->")
  //   edge((-1, -1), (0, -1), "->")
  //   edge((0, -1), (1, -1), "->")
  //   edge((1, -1), (2, -1), "->")
  //   edge((-2, 0), (-1, 0), "->")
  //   edge((-1, 0), (0, 0), "->")
  //   edge((0, 0), (1, 0), "->")
  //   edge((1, 0), (2, 0), "->")
  //   edge((-1, -1), (-1, 0), "hook'->")
  //   edge((0, -1), (0, 0), [$tilde$], label-side: center, "->")
  //   edge((1, -1), (1, 0), "->")
  // }, crossing-fill: thm-box-curr-color()))
  // 第一行在 $cPAb(X_et)$ 中正合，第一个竖直箭头是单射，因为 $im^(cPSh)(f)$ 分离。第二行在 $cPAb(X_et)$ 中正合，这一条留作练习。 

  // $cPAb(X_et), cAb(X_et)$ 有足够多的内射对象，这一点归功于 Grothendieck 的下述定理： 
  // #theorem[
  //   (Grothendieck in Touhoku) 若 $cal(C)$ 是满足 (Ab5) 公理、且有一族生成元的 Abel 范畴，则 $cal(C)$ 有足够多的内射对象。 
  // ]

  // - 我们直接接受 $cPAb(X_et), cAb(X_et)$ 满足 (Ab5)。至于 (Ab5) 是什么意思，我们不解释。 

  // - $(ZZ_V^\#)_(V in X_et)$ 构成 $cAb(X_et)$ 的一族生成元。也就是说，给定 $cal(F) subset.neq cal(G)$，可以取 $V$ 使 $cal(F)(V) subset.neq cal(G)(V)$。此时任取 $s in cal(G)(V) - cal(F)(V)$，就得到不穿过 $cal(F)$ 分解的态射 $ZZ_V^\# -> cal(G)$。 

  // (3) 由 (2) 得到，(4) 据称很容易。 
]

// 由 (3)，对 $cAb(X_et)$ 中的短正合列 $0 -> cal(F) -> cal(G) -> cal(H) -> 0$，有右正合列： 
// $
//   0 -> cal(F)(U) -> cal(G)(U) -> cal(H)(U)
// $
// 特别地，截面函子 $Gamma(U, -): cAb(X_et) -> cAb$ 左正合。 


#corollary(name: <sections-left-exact>)[
  截面函子 $Gamma(U, -): cAb(X_et) -> cAb$ 同构于 Hom 函子 $Hom(ul(ZZ)_(!,U), -)$，因此左正合。
]

#corollary[
  若 $cal(F) -> cal(G)$ 是单射，其中 $cal(F) in cPAb(X_et), cal(G) in cAb(X_et)$，则由伴随性诱导的 $cal(F)^\# -> cal(G)$ 是单射。 
]
#proof[
  这由 $(-)^\#$ 的正合性得到。 
]

在把 $cAb(X_et)$ 确立为有足够多内射对象的 Abel 范畴、并得到左正合函子 $Gamma(U, -)$ 之后，我们终于可以引入本课程的核心对象：

#definition(name: <defn-etale-cohomology>)[
  第 $n$ 个*平展上同调*函子 $H^n (U, -)$，定义为左正合函子 $Gamma(U, -): cAb(X_et) -> cAb$ 的第 $n$ 个右导出函子。 

  #notation[
    $X in X_et$ 是 $Et_X$ 的终对象。我们另外把平展景的上同调记作：
    $
      H^n_et (X, -) := H^n (X_et, -) := H^n (X, -): cAb(X_et) -> cAb
    $
  ]
]
