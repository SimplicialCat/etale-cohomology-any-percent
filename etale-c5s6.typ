#import "void-import.typ": *

== 域的谱 $Spec(K)_et$

本节篇幅很短。当 $X = Spec(K)$ 是域 $K$ 的谱时，我们要确定 $cSh(X_et)$ 与 $cAb(X_et)$ 的结构。 

#theorem(name: <struct-of-spec-k-et>)[
  在 $overline(x)$ 处的茎函子，即 $cal(F) |-> cal(F)_(overline(x)) = dirlim_(L\/K #[有限 Galois]) cal(F)(Spec(L))$，诱导出范畴等价： 
  $
    (-)_(ol(x)): cSh(Spec(K)_et) overset(->, tilde) GSet(Gal_K)^("disc,cont"), cAb(Spec(K)_et) overset(->, tilde) AMod(Gal_K)^("disc,cont")
  $
  其中上标 “disc,cont” 表示这些 $Gal_K$-集与模都带有离散拓扑，使 $Gal_K$ 在它们上面连续作用。 
  
  这里 $sigma in Gal_K$ 作用在 $cal(F)_(overline(x)) = dirlim_(L\/K #[有限 Galois]) cal(F)(Spec(L))$ 上：通过 $sigma$ 在 $Gal(L\/K)$ 中的像作用在 $cal(F)(Spec(L))$ 上。 
]
#proof[
  我们先对 $Et_(Spec(K))$ 作分类。 

  设 $X -> Spec(K)$ 平展。对任意点 $x in X$，由非分歧性的定义，$k(x)\/K$ 是有限可分域扩张。取 $x$ 附近的一个仿射开集 $Spec(A) subset X$，于是 $A$ 是有限型 $K$-代数。由于 $k(x)\/K$ 有限，$x$ 是 $Spec(A)$ 的闭点。由于 $x$ 是任取的，$Spec(A)$ 的每个点都是闭点。于是 $A$ 是 $0$ 维 Noether 环，从而是 Artin 环。故 $Spec(A)$ 只有有限多个点，而且这些点都既闭又开。又由 @etale-local-properties (4)，$X$ 是既约的。 
  
  总之： 
  $
    X = union.sq.big_(x in X) Spec(k(x))
  $
  其中每个 $k(x)\/K$ 都是有限可分扩张。反之，任何这种形式的概形都在 $Spec(K)$ 上平展，因此我们完成了 $Et_(Spec(K))$ 的分类。 

  为证明 $(-)_(ol(x)): cSh(Spec(K)_et) -> GSet(Gal_K)^("disc,cont")$ 是等价，我们直接构造它的拟逆： 
  $
    Phi: GSet(Gal_K)^#[disc,cont] -> cSh(Spec(K)_et), M |-> (Phi(M): union.sq.big_i Spec(L_i) |-> union.sq.big_i M^(Gal_L))
  $

  要证明 $Phi_M$ 是层：由于它与不交并相容，只需对每个覆盖 ${Spec(L) -> Spec(K)}$ 验证层条件。若 $N\/L\/K$ 是 $L\/K$ 的 Galois 闭包，则 $Spec(N) -> Spec(K)$ 是 $Spec(L) -> Spec(K)$ 的一个加细。 

  像 @etale-cover-equiv-conds 的证明那样用九引理追图，就只需对这些 $N\/K$ 验证层条件。现在有： 
  $
    N otimes_K N = product_(sigma in Gal(N\/K)) N
  $
  把对应于 $sigma$ 的因子记为 $N_sigma$。于是两个投影如下： 
  $
    p_(1,2): N otimes_K N -> N
  $
  其中 $p_1$ 在分量 $N_sigma -> N$ 上取恒等映射，$p_2$ 在分量 $N_sigma -> N$ 上取 $sigma$。从而 
  $
    ker(M^(Gal_N) -> product_(sigma in Gal(N\/K)) M^(Gal_N)) = inter.big_(sigma in Gal(N\/K)) (M^(Gal_N))^sigma = M^(Gal_K)
  $
  于是 $Phi(M)$ 的层条件验证完毕。剩下要证 $Phi$ 与 $(-)_(ol(x))$ 互为拟逆： 

  - #h(1fr)
    $
      (Phi(M))_(ol(x)) = dirlim_(L\/K #[有限可分]) M^(Gal_L) = M
    $
    因为 $M$ 的每个元素都在某个有限可分扩张 $L\/K$ 对应的 $Gal_L$ 作用下不变。 

  - 根据层条件，对任意 $cal(F) in cSh(Spec(K)_et)$，$cal(F)$ 由各个 $cal(F)(Spec(L))$ 决定。此外，对 Galois 扩张 $N\/L$，有 $cal(F)(Spec(L)) = cal(F)(Spec(N))^(Gal(N\/L))$。特别地，$cal(F)(Spec(L)) -> cal(F)(Spec(N))$ 是单射。对任意的有限可分扩张取 Galois 闭包，即知 $cal(F)$ 的限制映射都是单射。现在考虑： 
    $
      M = cal(F)_(ol(x)) = dirlim_(L\/K #[有限可分]) cal(F)(Spec(L))
    $
    由于所有限制映射都是单射，可以把 $cal(F)(Spec(L)) subset M$ 看成真正的包含关系。现在固定一个有限可分扩张 $T\/K$： 
    $
      M^(Gal_T) &= union.big_(L\/T #[有限可分]) cal(F)(Spec(L))^(Gal_T) = union.big_(L\/T #[有限 Galois]) cal(F)(Spec(L))^(Gal_T) \
      &= union.big_(L\/T #[有限 Galois]) cal(F)(Spec(L))^(Gal(L\/T)) = cal(F)(Spec(T))
    $
    至此我们证明了 $cal(F) cong Phi(M)$。 

  集合层的情形到此结束。至于交换群的情形，拟逆由下式给出： 
  $
    Phi: AMod(Gal_K)^#[disc,cont] -> cAb(Spec(K)_et), M |-> (Phi(M): union.sq.big_i Spec(L_i) |-> product_i M^(Gal_(L_i)))
  $
  论证完全一样。 
]

#corollary[
  我们有如下由范畴构成的交换图表： 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwwLCJjQWIoU3BlYyhLKV9ldCkiXSxbMiwwLCJHTW9kKEcpXlwiZGlzYyxjb250XCIiXSxbMSwyLCJjQWIiXSxbMCwyLCJHYW1tYShTcGVjKEspLCAtKSIsMl0sWzEsMiwiVCB8LT4gVF5HIl0sWzAsMSwidGlsZGUiXV0=
  #align(center, diagram({
    node((-1, -1), [$cAb(Spec(K)_et)$])
    node((1, -1), [$AMod(G)^"disc,cont"$])
    node((0, 0), [$cAb$])
    edge((-1, -1), (0, 0), [$Gamma(Spec(K), -)$], label-side: right, "->")
    edge((1, -1), (0, 0), [$T |-> T^G$], label-side: left, "->")
    edge((-1, -1), (1, -1), [$tilde$], label-side: left, "->")
  }))

  于是得到 $delta$-函子同构： 
  $
    H^q_et (Spec(K), cal(F)) cong H^q_"cont" (G, cal(F)_(overline(x)))// =: H^q (K, cal(F)_(overline(x)))
  $
  // 其中 $H^n (K, cal(F)_(overline(x)))$ 称为 Galois 上同调。这里 $H^n_"cont"$ 表示连续群上同调。 
  该同构连接平展上同调与连续群上同调。 
]

由平展上同调中的事实，可以推出连续 Galois 上同调中的事实： 

#corollary(name: <galois-cohom-props>)[
  0. /*回忆：对 $M in AMod(G)^"disc,cont"$，有： 
    $
      M = union.big_(K^sep\/L\/K "fin") M^(Gal(K^sep\/L))
    $
    于是我们有*/ 对任意离散 $Gal_K$-模 $M$，存在自然同构： #h(1fr)
    $
      H^q (Gal_K, M) cong dirlim_(L\/K #[有限 Galois]) H^q (Gal(L\/K), M^(Gal(K^sep\/L)))
    $
  
  + （极限公式）
    + 对由 $G$-模组成的余极限 $M = colim_i M_i$，有同构： 
      $
        colim_i H^q_"cont" (G, M_i) overset(->, tilde) H^q_"cont" (G, M)
      $

    + 对可分代数扩张 $K\/K_0$，$Gal_K$ 是 $Gal_(K_0) = Gal(K^sep\/K_0)$ 的闭子群；并且对 $N in AMod(Gal(K^sep\/K_0))$，有： 
      $
        colim_(K\/K_i\/K_0 \ K_i\/K_0 #[finite]) H^q_"cont" (Gal(K^sep\/K_i), N) overset(->, tilde) H^q_"cont" (Gal_K, N)
      $
  
  + (Hilbert 90) #h(1fr)
  
    // $G = Gal(K^sep\/K)$ 作用在 $(K^sep)^times, K^sep$ 上，并且： 
    // + (Hilbert 90) $H^1_"cont" (G, (K^sep)^times) = 0$，且 $H^2_"cont" (G, (K^sep)^times) = "Br"(K)$ 是（绝对）Brauer 群。 

    // + 
    //   $
    //   H^n_"cont" (G, K^sep) = cases(K &\, n = 0 , 0 &\, n >= 1)
    //   $

    + （加性 Hilbert 90 / $GG_a = cal(O)_(Spec(K),et)$ 的上同调） #h(1fr)
      $
        H^q_#[cont] (Gal_K, K^sep) = 0, forall q >= 1
      $

    + （乘性 Hilbert 90 / $GG_m$ 的 $H^1$）
      $
        H^1_#[cont] (Gal_K, (K^sep)^times) = 0// = Pic(Spec(K)) = 0
      $
      // （因为它等于 $H^1_et (Spec(K), GG_m) = Pic(Spec(K)) = 0$）

  + （常值层的 $H^1$）若 $G$ 平凡地作用在 $M$ 上，则： 
    $
      H^1_"cont" (Gal_K, M) = Hom_"cont" (Gal_K, M)
    $
]

// 下一节我们将讨论 (1)(2)(3) 的推广。 
