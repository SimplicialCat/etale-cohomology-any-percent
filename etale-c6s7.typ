#import "void-import.typ": *

== (Seed) 的证明

本章开头陈述的六点中，最后剩下的一点是 (Seed)。它讲的是限制映射 $H^q (X, ul(ZZ\/n)) -> H^q (X_0, ul(ZZ\/n))$ 有哪些性质，前提是 $A$ 为 Noether 的严格 Hensel 局部环、$X -> PP^1_A$ 有限。 

换言之，要得到一般的紧合基变换定理，剩下要证的只是一条关于射影 $1$ 维空间这个相当具体的情形的陈述。 

为证明所需结果，我们的证明大体分两步： 

+ 借助拓扑不变性，把 $X_0 = X otimes_A k$ 上的对象搬到 $X_n = X otimes_A A\/frak(m)^(n+1)$ 上，再取极限，得到 $hat(X) = X otimes_A hat(A)$ 上的对象。 

+ 把对象从完备化 $hat(A)$ 搬回 Hensel 局部环 $A$。 

这对应代数几何中的两个结果。它们本身就很有意思，证明也大体上是技术性的。第一步取决于 Grothendieck 存在定理，第二步取决于 Artin 逼近定理。 

本节对 (Seed) 的证明受 @cite-lei-fu 中证明的启发，只是 Artin 逼近的用法不同。

#theorem(name: <grothendieck-existence-thm>)[
  (Grothendieck 存在定理 + 形式函数定理) 

  #definition[
    给定 Noether 概形 $X$，令 $cal(I) subset cal(O)_X$ 为凝聚理想层。定义范畴 $Coh(X, cal(I))$ 为如下范畴：其对象是满足下列条件的凝聚 $cal(O)_X$-模逆向系统 ${cal(F)_n}_(n>=1)$：
    
    + 对每个 $n$，$cal(I)^n cal(F)_n = 0$；
    
    + 过渡映射 $cal(F)_(n+1) -> cal(F)_n$ 诱导同构 $cal(F)_(n+1)\/cal(I)^n cal(F)_(n+1) -> cal(F)_n$。
    
    换言之，可以把 $cal(F)_n in Coh(X_n)$ 连同同构 $phi_n: i_n^* cal(F)_(n+1) cong cal(F)_n$ 一起来看，其中 $X_n := SPec(cal(O)_X\/cal(I)^n)$；这些同构沿如下的正向系统：
    $
      X_1 -> dots.c -> X_n ->^(i_n) X_(n+1) -> dots.c
    $
  ]
  给定 Noether 环 $A$、使 $A$ 完备的理想 $I$，以及 $Spec(A)$ 上的紧合概形 $X$，则有范畴等价： 
  $
    hat: Coh(X) &-> Coh(X, I cal(O)_X) \
    cal(F) &|-> {cal(F)\/I^n cal(F)}_(n>=1)
  $
  此外，它还诱导典范同构： 
  $
    H^q (X, cal(F)) = invlim_(n>=1) H^q (X_n, cal(F)\/cal(I)^n cal(F))
  $
]
#proof[
  请读者阅读 #cite-stacks("088C")[Proposition 30.25.4]。 

  展开 Stacks Project 中某个结果的证明时，若做深度优先式的上下文检索，负担会很重；为减轻这一负担，我们建议读者按顺序阅读 #cite-stacks("0EHN,087V,0886")[Section 30.23\~30.25]。 

  关于上同调的那条陈述就是形式函数定理，见 #cite-stacks("02OC")[Theorem 30.20.5]。 
]

Artin 逼近的陈述见 @artin-approximation-theorem，证明见 @appendix-artin-approximation。 

下面分别证明 (Seed) 在 0、1、2 次上的前置结果，因为由 @cohom-of-general-curve，我们预计 $>=3$ 次会消没。0 次的情形已在 @pbc-seed-precursor-0 中处理，现在处理 1 次的情形。 

#proposition(name: <pbc-seed-precursor-1>)[
  设 $(A, frak(m), k)$ 是 Noether 的 Hensel 局部环，$X -> Spec(A)$ 紧合。则基变换： 
  $
    FEt_X -> FEt_(X_0), Y |-> Y_0 := Y times_X X_0
  $
  是范畴等价。特别地，诱导的映射：
    $
      pi_1^et (X_0, ol(x)) -> pi_1^et (X, ol(x))
    $
    对 $X_0$ 的任意几何点 $ol(x)$ 都是同构。 
]
#proof[
  先直接证明全忠实。固定 $X_0$ 的一个几何点 $ol(x)$。则对 $Y, Z in FEt_X$： 
  $
    Hom_X (Y, Z) cong Hom_(pi_1^et (X, ol(x))) (F_(ol(x)) (Y), F_(ol(x)) (Z)) \
    Hom_(X_0) (Y_0, Z_0) cong Hom_(pi_1^et (X_0, ol(x))) (F_(ol(x)) (Y_0), F_(ol(x)) (Z_0))
  $
  现在两个纤维集分别满足 $F_(ol(x)) (Y) cong F_(ol(x)) (Y_0), F_(ol(x)) (Z) cong F_(ol(x)) (Z_0)$。因此，只要能证明： 
  $
    pi_1^et (X_0, ol(x)) -> pi_1^et (X, ol(x))
  $
  满射，从而把 $pi_1^et (X, ol(x))$ 看成 $pi_1^et (X_0, ol(x))$ 的商，就完成了。由 @pi1et-mor-props，只需证明：对任意连通的 $Y in FEt_X$，$Y_0$ 都连通。这正是 @pbc-seed-precursor-0。 

  剩下只需证本质满性。先做一个极限论证： 

  - 把 $A$ 写成其有限型 $ZZ$-子代数的正向极限：$A = dirlim_i A_i$。由于 $A$ 是局部环，而局部化与正向极限交换，
    $
      A = A_(frak(m)) = dirlim_i (A_i)_(frak(p)_i)
    $
    其中 $frak(p)_i = frak(m) ∩ A_i$。这就把 $A$ 写成了若干子代数的正向极限，而这些子代数都是有限型 $ZZ$-代数在素理想处的局部化。最后，由 @henselization-and-directed-limits，Hensel 化与正向极限交换：
    $
      A = A^#[h] = dirlim_i (A_i)_(frak(p)_i)^#[h]
    $
  于是它是有限型 $ZZ$-代数在素理想处作 Hensel 化所得的正向极限，过渡映射都是局部的。 

    把这个正向极限改记为 $A = dirlim_lambda A_lambda$。 
    
    由 @passage-to-limit-of-morphisms (1) 与 @passage-to-limit-of-properties (2e)，适当截断正向集 ${lambda}$，不妨设 $X -> Spec(A)$ 由某个紧合的 $X_lambda -> Spec(A_lambda)$ 经基变换得到。对 $mu >= lambda$，记 $X_mu = X_lambda otimes_(A_lambda) A_mu$，并记 $X_(mu,0)$ 为把它沿 $Spec(A_mu)$ 的闭点作基变换所得。 

    由 @passage-to-limit-of-properties (2a)(3d)， 
    $
      FEt_X cong dirlim_(mu>=lambda) FEt_(X_mu) \
      FEt_(X_0) cong dirlim_(mu>=lambda) FEt_(X_(mu,0))
    $
    因此只需证明每个 $FEt_(X_mu) -> FEt_(X_(mu,0))$ 都是范畴等价。 

  于是不妨设 $A$ 是某个有限型 $ZZ$-代数在素理想处的 Hensel 化。记 $hat(A)$ 为 $A$ 的完备化，$hat(X) = X otimes_A hat(A)$。我们先断言： 
  $
    FEt_(hat(X)) -> FEt_(X_0)
  $
  本质满。 

  - 对每个 $m>=0$，记 $X_m = X otimes_A A\/frak(m)^(m+1)$。#h(1fr)
  
    任取 $Y_0 in FEt_(X_0)$。由拓扑不变性（@top-invariance-sheaves (3)），存在 $Y_m in FEt_(X_m)$，使得 $Y_m cong Y_(m+1) times_(X_(m+1)) X_m$，且这些同构彼此相容。记 $phi_m: Y_m -> X_m$ 为结构映射，$cal(F)_m = phi_(m,*) cal(O)_(Y_m)$。 

    则每个 $cal(F)_m$ 都是凝聚的 $cal(O)_(X_m)$-代数层，且满足 $cal(F)_(m+1) otimes_(A\/frak(m)^(m+2)) A\/frak(m)^(m+1) cong cal(F)_m$。由 @grothendieck-existence-thm，存在凝聚的 $cal(O)_(hat(X))$-模层 $hat(cal(F))$，使得：
    $
      cal(F)_m cong hat(cal(F)) otimes_(hat(A)) A\/frak(m)^(m+1)
    $
    现在由形式函数定理（见 @grothendieck-existence-thm）， 
    $
      Hom_(cal(O)_(hat(X))) (hat(cal(F)) otimes_(cal(O)_(hat(X))) hat(cal(F)), hat(cal(F))) cong invlim_(m>=0) Hom_(cal(O)_(X_m)) (cal(F)_m otimes_(cal(O)_(X_m)) cal(F)_m, cal(F)_m)
    $
    于是每个 $cal(F)_m$ 上的乘法都能提升到 $hat(cal(F))$。结合律、交换律与单位元则由形式函数定理，从各个 $X_m$ 上对应的关系提升得到。例如交换律，可通过把对称同构沿下式提升来验证： 
    $
      & Hom_(cal(O)_(hat(X))) (HHom_(cal(O)_(hat(X))) (hat(cal(F)) otimes_(cal(O)_(hat(X))) hat(cal(F)), hat(cal(F))), HHom_(cal(O)_(hat(X))) (hat(cal(F)) otimes_(cal(O)_(hat(X))) hat(cal(F)), hat(cal(F)))) \
      cong& invlim_(m>=0) Hom_(cal(O)_(X_m)) (HHom_(cal(O)_(X_m)) (cal(F)_m otimes_(cal(O)_(X_m)) cal(F)_m, cal(F)_m), HHom_(cal(O)_(X_m)) (cal(F)_m otimes_(cal(O)_(X_m)) cal(F)_m, cal(F)_m))
    $
    其余环公理都是例行公事，不再逐一验证。于是可把 $hat(cal(F))$ 等同于凝聚的 $cal(O)_(hat(X))$-代数层，且满足 $cal(F)_m cong hat(cal(F)) otimes_(hat(A)) A\/frak(m)^(m+1)$。令 $hat(Y) = SPec(hat(cal(F)))$，则 $hat(phi): hat(Y) -> hat(X)$ 是有限映射，而它基变换后正是各个 $phi_m$。平展性由下面的引理保证，于是证毕。  
    #lemma[
      设 $(A, frak(m))$ 是 Noether 的完备局部环，$f: X -> Y$ 是有限 $A$-概形之间的态射，且对每个 $m>=0$，沿 $Spec(A\/frak(m)^(m+1)) -> Spec(A)$ 的基变换 $f_m: X_m -> Y_m$ 都平展，则 $f$ 有限平展。 
    ]
    #proof[
      平展性可在目标上局部验证，故不妨设 $X = Spec(C), Y = Spec(B)$，其中 $B, C$ 是有限 $A$-代数。令 $X_m = Spec(C_m), Y_m = Spec(B_m)$。 
      
      $f$ 非分歧，因为： 
      $
        Omega_(C\/B) otimes_A A\/frak(m) cong Omega_(C_0\/B_0) = 0
      $
      故 $Omega_(C\/B) = frak(m) Omega_(C\/B)$。由 Nakayama 引理，$Omega_(C\/B) = 0$。 

      对任意极大理想 $frak(q) in Spec(B)$，我们要证 $C_(frak(q))$ 在 $B_(frak(q))$ 上自由。由于 $B$ 在 $A$ 上有限，$frak(q)$ 落在极大理想 $frak(m) in Spec(A)$ 之上，即 $frak(q) B_(frak(q)) supset frak(m) B_(frak(q))$。 

      由于每个 $f_m$ 有限平坦，每个 $B_(frak(q))\/frak(m)^(m+1) B_(frak(q)) -> C_(frak(q))\/frak(m)^(m+1) C_(frak(q))$ 都有限平坦。又因 $B_(frak(q))\/frak(m)^(m+1) B_(frak(q))$ 是局部环，其上的模因而自由。它们的秩都等于同一个 $r$。 

      取 $C_(frak(q))\/frak(m) C_(frak(q))$ 在 $B_(frak(q))\/frak(m) B_(frak(q))$ 上的一组基 $[c_1], dots.c, [c_r]$，并把它们任意提升为 $c_1, dots.c, c_r$。则： 
      $
        C_(frak(q)) = sum_(i=1)^r B_(frak(q)) c_i + frak(m) C_(frak(q))
      $
      现在 $C_(frak(q))$ 是有限 $B_(frak(q))$-模，而 $frak(m) B_(frak(q)) subset frak(q) B_(frak(q))$，后者是极大理想。于是由 Nakayama，$C_(frak(q)) = sum_(i=1)^r B_(frak(q)) c_i$。因此，由 $c_1, dots.c, c_r$ 定义的映射： 
      $
        phi: B_(frak(q))^(oplus r) -> C_(frak(q))
      $
      是满射。模去每个 $frak(m)^(m+1)$，它是两个同秩自由模之间的满射，从而是双射。换言之， 
      $
        ker(phi) subset inter.big_(m>=0) frak(m)^(m+1) B_(frak(q))^(oplus r)
      $
      由 Krull 交定理，这个核为零，故 $phi$ 是双射。 
    ]

  既然 $FEt_(hat(X)) -> FEt_(X_0)$ 本质满，就可以用 Artin 逼近来完成证明。考虑函子： 
  $
    F: AAlg(A) -> cSet, B |-> FEt_(X otimes_A B)\/cong
  $
  它把 $B$ 送到 $X otimes_A B$ 的有限平展覆叠的同构类。由 @passage-to-limit-of-morphisms (2)(3) 与 @passage-to-limit-of-properties (2a)(3d)，$F$ 与正向极限交换。既然 $FEt_(hat(X)) -> FEt_(X_0)$ 本质满，任意 $Y_0 in F(A\/frak(m))$ 都能提升为某个 $hat(Y) in F(hat(A))$。 
  
  而 $A$ 是有限型 $ZZ$-代数在素理想处的 Hensel 化，故它或是某个 $QQ$ 上的有限型代数在素理想处的 Hensel 化、或是某个 $ZZ_((p))$ 上的有限型代数在素理想处的 Hensel 化，取决于 $A$ 的极大理想落在 $ZZ$ 的哪个素理想之上。$QQ$ 是域，$ZZ_((p))$ 是优良的 DVR，因此 Artin 逼近适用。 
  
  由 Artin 逼近（@artin-approximation-theorem (2)），存在 $Y in F(A)$，使得 $Y$ 与 $hat(Y)$ 转到 $F(A\/frak(m))$ 后一致。也就是说，$Y otimes_A A\/frak(m) cong hat(Y) otimes_(hat(A)) A\/frak(m) cong Y_0$。至此证明了本质满性。 
]

接下来处理 2 次的情形。 
#proposition(name: <pbc-seed-precursor-2>)[
  设 $(A, frak(m), k)$ 是 Noether 的 Hensel 局部环，$X -> Spec(A)$ 紧合。若 $X$ 的特殊纤维 $X_0$ 满足 $dim(X_0) <= 1$，则基变换映射： 
  $
    Pic(X) -> Pic(X_0)
  $
  是满射。 
]
#proof[
  与 @pbc-seed-precursor-1 的证明中那个断言的做法类似，可写 $A = dirlim_lambda A_lambda$，其中每个 $A_lambda$ 都是有限型 $ZZ$-代数在素理想处的 Hensel 化，且所有过渡映射都是局部的。由 @passage-to-limit-of-morphisms (2) 与 @passage-to-limit-of-properties (2e)，$X -> Spec(A)$ 来自某个紧合的 $X_lambda -> Spec(A_lambda)$。 

  #lemma[
    设 $X = invlim_lambda X_lambda$ 是拟紧拟分离概形的逆向极限，过渡映射都是仿射的。则： 
    $
      Pic(X) cong dirlim_lambda Pic(X_lambda)
    $
  ]
  #proof[
    @passage-to-limit-of-sheaves (1)(2)(3) 实际上是在说： 
    $
      Coh(X)/cong cong dirlim_lambda Coh(X_lambda)/cong
    $
    也就是说，有限展示的 $cal(O)_X$-模层的同构类，正是有限展示的 $cal(O)_(X_lambda)$-模层的同构类的正向极限。过渡映射也是幺半的，即与张量积相容。于是对可逆层也有同样的极限公式，从而： 
    $
      Pic(X) cong dirlim_lambda Pic(X_lambda)
    $
  ]
  由上一个引理， 
  $
    Pic(X) = dirlim_lambda Pic(X_lambda) \
    Pic(X_0) = dirlim_lambda Pic(X_(lambda,0))
  $
  因此只需证明每个 $Pic(X_lambda) -> Pic(X_(lambda,0))$ 都是满射。于是不妨设 $A$ 是有限型 $ZZ$-代数的 Hensel 化。 

  记 $hat(A)$ 为 $A$ 的完备化，$hat(X) = X otimes_A hat(A)$。我们断言 $Pic(hat(X)) -> Pic(X_0)$ 是满射。 

  - 令 $X_n = X otimes_A A\/frak(m)^(n+1)$，它与 $X_0$ 有相同的底空间。对 $n>=0$，考虑 $X_0$ 上 Zariski 层的正合列： 
    $
      0 -> frak(m)^(n+1) cal(O)_X -->^(gamma |-> 1+gamma) (cal(O)_X\/frak(m)^(n+2) cal(O)_X)^times -> (cal(O)_X\/frak(m)^(n+1) cal(O)_X)^times -> 0
    $
    取上同调长正合列，得到： 
    $
      dots.c -> H^1_#[Zar] (X_0, (cal(O)_X\/frak(m)^(n+2) cal(O)_X)^times) -> H^1_#[Zar] (X_0, (cal(O)_X\/frak(m)^(n+1) cal(O)_X)^times) -> H^2_#[Zar] (X_0, frak(m)^(n+1) cal(O)_X) -> dots.c
    $
    即： 
    $
      dots.c -> Pic(X_(n+1)) -> Pic(X_n) -> H^2_#[Zar] (X_0, frak(m)^(n+1)) -> dots.c
    $
    由于 $dim(X_0) <= 1$，而 Zariski 上同调在超过这个维数的次数上消没，故 $H^2_#[Zar] (X_0, frak(m)^(n+1)) = 0$，从而每个 $Pic(X_(n+1)) -> Pic(X_n)$ 都是满射。 
  
    我们断言 $Pic(hat(X)) = invlim_(n>=0) Pic(X_n)$。 
    #proof_[断言的证明][
      由 Grothendieck 存在定理（@grothendieck-existence-thm），作为集合， 
      $
        {cal(L) in Coh(hat(X)): j_n^* cal(L) in Pic(X_n)}/cong = invlim_(n>=0) Pic(X_n)
      $
      其中 $j_n: X_n -> hat(X)$。现在设 $cal(L) in Coh(hat(X))$，且每个 $j_n^* cal(L)$ 可逆，我们来证明它本身可逆。令 $cal(M)_n = (j_n^* cal(L))^(otimes (-1))$。则对 $i_n: X_n -> X_(n+1)$， 
      $
        i_n^* cal(M)_(n+1) cong (i_n^* j_(n+1)^* cal(L))^(otimes (-1)) cong (j_n^* cal(L))^(otimes (-1)) cong cal(M)_n
      $
      于是由 @grothendieck-existence-thm，${cal(M)_n}$ 构成 $Coh(hat(X), frak(m) cal(O)_(hat(X)))$ 中的一个对象，并来自某个层 $cal(M) in Coh(hat(X))$。由此对每个 $n$ 都有 $j_n^* (cal(L) otimes cal(M)) cong cal(O)_(X_n)$，故由 @grothendieck-existence-thm，$cal(L) otimes cal(M) cong cal(O)_(hat(X))$。 
      #suppress-qed
    ]
    既然 $Pic(hat(X)) = invlim_(n>=0) Pic(X_n)$，且每个 $Pic(X_(n+1)) -> Pic(X_n)$ 都是满射，$Pic(hat(X)) -> Pic(X_0)$ 也必然是满射。 
  
  而 $A$ 是有限型 $ZZ$-代数在素理想处的 Hensel 化，故它或是某个 $QQ$ 上的有限型代数在素理想处的 Hensel 化、或是某个 $ZZ_((p))$ 上的有限型代数在素理想处的 Hensel 化，取决于 $A$ 的极大理想落在 $ZZ$ 的哪个素理想之上。$QQ$ 是域，$ZZ_((p))$ 是优良的 DVR，因此 Artin 逼近在 $A$ 上适用。考虑函子： 
  $
    F: AAlg(A) -> cSet, B |-> Pic(X otimes_A B)
  $ 
  我们已经证明它与正向极限交换。任取 $cal(L)_0 in Pic(X_0)$，把它提升为 $hat(cal(L)) in Pic(hat(X))$。再由 Artin 逼近（@artin-approximation-theorem (2)），存在 $cal(L) in Pic(X)$，使它拉回到 $X_0$ 后与 $hat(cal(L))$ 一致。也就是说，$cal(L)$ 拉回到 $X_0$ 后就是 $cal(L)_0$。于是 $Pic(X) -> Pic(X_0)$ 是满射。 
]

最后处理 $>=3$ 次的情形，这归结为一条消没结果。 
#proposition(name: <pbc-seed-precursor-3>)[
  设 $k$ 是可分闭域，$X_0$ 在 $k$ 上紧合，且 $dim(X_0) <= 1$。则： 

  + #h(1fr)
    $
      H^q_et (X_0, ul(ZZ\/n)) = 0
    $
    对所有 $q>=3$ 成立；若 $n = p^a$ 且 $p = "char"(k) > 0$，则对 $q=2$ 也成立。 

  + $
      H^q_et (X_0, GG_m) = 0
    $
    对所有 $q>=2$ 成立。 
]
#proof[
  记 $ol(k)$ 为 $k$ 的代数闭包，则 $ol(k)\/k$ 是纯不可分的代数扩张。现在 $dim(X_0 otimes_k ol(k)) = dim(X_0) <= 1$。由拓扑不变性，可以把 $X_0$ 换成 $X_0 otimes_k ol(k)$，再换成它的约化，从而不妨设 $k$ 代数闭、$X_0$ 既约。 

  (1) 中 $q>=3$ 的部分由 @grothendieck-vanishing-in-dim-1 解决。因此对 (1) 只需证明 $H^2 (X_0, ul(ZZ\/p^a)) = 0$。若 $X_0$ 整，则已经完成：(1) 由 @cohom-of-proj-curve (3) 解决，(2) 由 @cohom-of-gm-on-general-curve 解决。 
  
  一般情形下，设 $X_1, dots.c, X_s$ 是 $X_0$ 的不可约分支，并带有既约诱导子概形结构。令 $U = X_0 - union.big_(1<=i<j<=s) (X_i inter X_j)$ 为 $X_0$ 中只落在一个不可约分支里的点集。则 $U$ 是 $X_0$ 的开集，而 $Z = X_0 - U$ 是 $X_0$ 中有限个闭点构成的集合，带有既约诱导子概形结构。由于 $k$ 代数闭，$Z = union.sq.big_(z in Z) Spec(k)$。另外取 $U_i = X_i ∩ U$ 为 $X_i$ 中不在其他任何不可约分支里的点集。用 $f_i: X_i -> X_0$ 表示这些包含映射。 

  给定层 $cal(F) in cAb(X_et)$，考虑自然映射 $cal(F) -> oplus.big_(i=1)^s f_(i,*) f_i^(-1) cal(F)$。在茎上，它是如下的对角嵌入： 
  $
    cal(F)_(ol(x)) |-> oplus.big_(i: x in X_i) cal(F)_(ol(x))
  $
  它对所有 $x in X$ 都是单射，当 $x in U$ 时还是双射。于是取余核，得到正合列： 
  $
    0 -> cal(F) -> oplus.big_(i=1)^s f_(i,*) f_i^(-1) cal(F) -> cal(R) -> 0
  $
  其中 $cal(R)|_U = 0$。令 $j: Z -> X$ 为包含映射，则由 @pushforward-by-closed-immersion (2)，存在 $cal(G) in cAb(Z_et)$ 使 $cal(R) = j_* cal(G)$。现在作长正合列，并用 @pushforward-by-finite-morphism： 
  $
    dots.c -> H^(q-1) (Z, cal(G)) -> oplus.big_(i=1)^s H^q (X_i, f_i^(-1) cal(F)) -> H^q (X, cal(F)) -> H^q (Z, cal(G)) -> dots.c
  $
  由于 $Z = union.sq.big_(z in Z) Spec(k)$，只要 $q>=2$（从而 $q-1>=1$），由 @struct-of-spec-omega-et 就有 $H^(q-1) (Z, cal(G)) = H^q (Z, cal(G)) = 0$。因此， 
  $
    H^q (X, cal(F)) cong oplus.big_(i=1)^s H^q (X_i, f_i^(-1) cal(F)), q >= 2
  $

  (1) 取 $cal(F) = ul(ZZ\/p^a)$，并对每个整的 $X_i$ 应用上述结果，即完成证明。 

  (2) 由上面的论证，我们有： 
  $
    H^q (X, GG_m) cong oplus.big_(i=1)^s H^q (X_i, f_i^(-1) GG_m), q >= 2
  $
  现在考虑典范映射 $phi: f_i^(-1) GG_(m,X) -> GG_(m,X_i)$。由于 $f_i|_(U ∩ X_i): U ∩ X_i -> U$ 是同构，可见 $phi: f_i^(-1) GG_(m,X) -> GG_(m,X_i)$ 限制到 $U ∩ X_i$ 上是同构。现在取其核与余核： 
  $
    0 -> cal(K) -> f_i^(-1) GG_(m,X) ->^phi GG_(m,X_i) -> cal(R) -> 0
  $
  其中 $cal(K)|_(U∩X_i) = cal(R)|_(U∩X_i) = 0$。由 @pushforward-by-closed-immersion (2)，$cal(K), cal(R)$ 是 $Z ∩ X_i = union.sq.big_(z in Z ∩ X_i) Spec(k)$ 上的层的推前，而后者是一族剩余域为 $k$ 的闭点。由 @pushforward-by-finite-morphism 与 @struct-of-spec-omega-et，可见对所有 $q >= 1$ 都有 $H^q (X_i, cal(K)) = H^q (X_i, cal(R)) = 0$。因此，只要 $q >= 2$，用长正合列： 
  $
    H^q (X_i, f_i^(-1) GG_(m,X)) cong H^q (X_i, im(phi)) cong H^q (X_i, GG_m) = 0
  $
  其中对整的 $X_i$ 用上了 $GG_m$ 的上同调结果。 
]

现在终于可以证明 (Seed) 了。 

#theorem[
  (Seed) 设 $(A, frak(m), k)$ 是严格 Hensel 局部环，$X -> PP^1_A$ 有限。令 $X_0 = X otimes_A k$。则对所有自然数 $n>=1$，限制映射： 
  $
    H^q (X, ul(ZZ\/n)) -> H^q (X_0, ul(ZZ\/n))
  $
  在 $q = 0$ 时是同构，在 $q >= 1$ 时是满射。 
]
#proof[
  我们对每个次数分别证明。 

  - $q = 0$ 的情形由 @pbc-point-deg0 解决。 

  - $q = 1$ 的情形： 
    由 @pbc-seed-precursor-0，不妨设 $X$ 与 $X_0$ 连通。现在由 @h1-of-const-sheaf，限制态射 $H^1 (X, ul(ZZ\/n)) -> H^1 (X_0, ul(ZZ\/n))$ 就是： 
    $
      Hom_#[cont] (pi_1^et (X, ol(x)), ZZ\/n) -> Hom_#[cont] (pi_1^et (X_0, ol(x)), ZZ\/n)
    $
    它由态射 $pi_1^et (X_0, ol(x)) -> pi_1^et (X, ol(x))$ 诱导，而后者由 $X_0 -> X$ 诱导。由 @pbc-seed-precursor-1，$pi_1^et (X_0, ol(x)) -> pi_1^et (X, ol(x))$ 是连续同构，故 $Hom_#[cont] (pi_1^et (X, ol(x)), ZZ\/n) -> Hom_#[cont] (pi_1^et (X_0, ol(x)), ZZ\/n)$ 是同构。 

  - $q = 2$ 的情形： 
    由 @pbc-seed-precursor-3，只要 $p = "char"(k) > 0$ 就有 $H^2 (X_0, ZZ\/p^a) = 0$。因此，把 $p$-部分作为直和项分离出去，便可假设 $n in k^times$。由于 $A$ 是局部环，$n in k^times$ 说明它在 $A$ 中可逆，故 $n in A^times$。 

    固定一个本原 $n$ 次单位根 $zeta in k^times$，并把它提升为本原 $n$ 次单位根 $zeta in A^times$。由 @mu-n-is-zn，$zeta$ 诱导同构： 
    $
      mu_(n,X) cong ul(ZZ\/n)_X \
      mu_(n,X_0) cong ul(ZZ\/n)_(X_0)
    $
    这些同构与拉回相容。因此只需证明限制映射 $H^2 (X, mu_n) -> H^2 (X_0, mu_n)$ 是满射。令 $i: X_0 -> X$ 为包含映射，考虑 Kummer 序列： 
    $
      0 -> mu_(n,X) -> GG_(m,X) ->^((-)^n) GG_(m,X) -> 0
    $
    沿 $i$ 拉回，得到另一个正合列： 
    $
      0 -> i^(-1) mu_(n,X) -> i^(-1) GG_(m,X) ->^((-)^n) i^(-1) GG_(m,X) -> 0
    $
    我们断言：典范同构 $i^(-1) mu_(n,X) cong mu_n$（由上文与常值层的等同建立）与典范态射 $i^(-1) GG_(m,X) -> GG_(m,X_0)$ 可以放进一个交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsMTAsWzAsMCwiMCJdLFsxLDAsImleKC0xKSBtdV8obixYKSJdLFsyLDAsImleKC0xKSBHR18obSxYKSJdLFszLDAsImleKC0xKSBHR18obSxYKSJdLFs0LDAsIjAiXSxbMCwxLCIwIl0sWzEsMSwibXVfKG4sWF8wKSJdLFsyLDEsIkdHXyhtLFhfMCkiXSxbMywxLCJHR18obSxYXzApIl0sWzQsMSwiMCJdLFswLDFdLFsxLDJdLFsyLDMsIigtKV5uIl0sWzMsNF0sWzUsNl0sWzYsN10sWzcsOCwiKC0pXm4iLDJdLFs4LDldLFsxLDZdLFsyLDddLFszLDhdXQ==
    #align(center, diagram({
      node((-1, -1), [$0$])
      node((0, -1), [$i^(-1) mu_(n,X)$])
      node((1, -1), [$i^(-1) GG_(m,X)$])
      node((2, -1), [$i^(-1) GG_(m,X)$])
      node((3, -1), [$0$])
      node((-1, 0), [$0$])
      node((0, 0), [$mu_(n,X_0)$])
      node((1, 0), [$GG_(m,X_0)$])
      node((2, 0), [$GG_(m,X_0)$])
      node((3, 0), [$0$])
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), "->")
      edge((1, -1), (2, -1), [$(-)^n$], label-side: left, "->")
      edge((2, -1), (3, -1), "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0), [$(-)^n$], label-side: right, "->")
      edge((2, 0), (3, 0), "->")
      edge((0, -1), (0, 0), "->")
      edge((1, -1), (1, 0), "->")
      edge((2, -1), (2, 0), "->")
    }))
    右边的方块当然交换，因为乘以 $n$ 和什么都交换。至于左边的方块，用伴随性，只需证明下面的方块交换： 
    // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJtdV8obixYKSJdLFswLDEsImlfKiBtdV8obixYKSJdLFsxLDAsIkdHXyhtLFgpIl0sWzEsMSwiaV8qIEdHXyhtLFgpIl0sWzAsMiwiIiwwLHsic3R5bGUiOnsidGFpbCI6eyJuYW1lIjoiaG9vayIsInNpZGUiOiJ0b3AifX19XSxbMCwxXSxbMiwzXSxbMSwzLCIiLDIseyJzdHlsZSI6eyJ0YWlsIjp7Im5hbWUiOiJob29rIiwic2lkZSI6InRvcCJ9fX1dXQ==
    #align(center, diagram({
      node((0, -1), [$mu_(n,X)$])
      node((0, 0), [$i_* mu_(n,X_0)$])
      node((1, -1), [$GG_(m,X)$])
      node((1, 0), [$i_* GG_(m,X_0)$])
      edge((0, -1), (1, -1), "hook->")
      edge((0, -1), (0, 0), "->")
      edge((1, -1), (1, 0), "->")
      edge((0, 0), (1, 0), "hook->")
    }))
    事实上，态射 $GG_(m,X) -> i_* GG_(m,X_0)$ 在截面上是 $cal(O)_X (U)^times -> cal(O)_(X_0) (U_0)^times$，这个映射由结构映射 $U_0 -> U$ 诱导；$mu_(n,X) -> i_* mu_(n,X_0)$ 同理。转到长正合列，得到交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsMTUsWzAsMCwiZG90cy5jIl0sWzQsMCwiZG90cy5jIl0sWzEsMCwiSF4xIChYLCBHR19tKSJdLFsyLDAsIkheMiAoWCwgbXVfbikiXSxbMywwLCJIXjIgKFgsIEdHX20pIl0sWzAsMSwiZG90cy5jIl0sWzAsMiwiZG90cy5jIl0sWzQsMSwiZG90cy5jIl0sWzQsMiwiZG90cy5jIl0sWzEsMSwiSF4xIChYXzAsIGleKC0xKSBHR19tKSJdLFsyLDEsIkheMiAoWF8wLCBtdV9uKSJdLFszLDEsIkheMiAoWF8wLCBpXigtMSkgR0dfbSkiXSxbMSwyLCJIXjEgKFhfMCwgR0dfbSkiXSxbMywyLCJIXjIgKFhfMCwgR0dfbSkiXSxbMiwyLCJIXjIgKFhfMCwgbXVfbikiXSxbMCwyXSxbMiwzXSxbMyw0XSxbNCwxXSxbNSw5XSxbOSwxMF0sWzEwLDExXSxbMTEsN10sWzYsMTJdLFsxMiwxNF0sWzE0LDEzXSxbMTMsOF0sWzIsOV0sWzksMTJdLFszLDEwXSxbMTAsMTQsIiIsMSx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFs0LDExXSxbMTEsMTNdXQ==
    #align(center, diagram({
      node((-2, -1), [$dots.c$])
      node((2, -1), [$dots.c$])
      node((-1, -1), [$H^1 (X, GG_m)$])
      node((0, -1), [$H^2 (X, mu_n)$])
      node((1, -1), [$H^2 (X, GG_m)$])
      node((-2, 0), [$dots.c$])
      node((-2, 1), [$dots.c$])
      node((2, 0), [$dots.c$])
      node((2, 1), [$dots.c$])
      node((-1, 0), [$H^1 (X_0, i^(-1) GG_m)$])
      node((0, 0), [$H^2 (X_0, mu_n)$])
      node((1, 0), [$H^2 (X_0, i^(-1) GG_m)$])
      node((-1, 1), [$H^1 (X_0, GG_m)$])
      node((1, 1), [$H^2 (X_0, GG_m)$])
      node((0, 1), [$H^2 (X_0, mu_n)$])
      edge((-2, -1), (-1, -1), "->")
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), "->")
      edge((1, -1), (2, -1), "->")
      edge((-2, 0), (-1, 0), "->")
      edge((-1, 0), (0, 0), "->")
      edge((0, 0), (1, 0), "->")
      edge((1, 0), (2, 0), "->")
      edge((-2, 1), (-1, 1), "->")
      edge((-1, 1), (0, 1), "->")
      edge((0, 1), (1, 1), "->")
      edge((1, 1), (2, 1), "->")
      edge((-1, -1), (-1, 0), "->")
      edge((-1, 0), (-1, 1), "->")
      edge((0, -1), (0, 0), "->")
      edge((0, 0), (0, 1), "=")
      edge((1, -1), (1, 0), "->")
      edge((1, 0), (1, 1), "->")
    }))
    其中第一行的竖直箭头是限制映射，第二行则由上文建立的短正合列交换图表诱导。现在用 @h1-of-gm-is-pic 并展开定义，可见第一列竖直箭头正是 $Pic(X) -> Pic(X_0)$，而 @pbc-seed-precursor-2 说明它是满射。又由 @pbc-seed-precursor-3，$H^2 (X_0, GG_m) = 0$。于是得到交换图表： 
    // https://q.uiver.app/#r=typst&q=WzAsOSxbMCwwLCJkb3RzLmMiXSxbMSwwLCJQaWMoWCkiXSxbMiwwLCJIXjIgKFgsIG11X24pIl0sWzMsMCwiSF4yIChYLCBHR19tKSJdLFs0LDAsImRvdHMuYyJdLFszLDEsIjAiXSxbMCwxLCJkb3RzLmMiXSxbMSwxLCJQaWMoWF8wKSJdLFsyLDEsIkheMiAoWF8wLCBtdV9uKSJdLFswLDFdLFsxLDJdLFsyLDNdLFszLDRdLFs2LDddLFs3LDgsIiIsMCx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFs4LDVdLFsxLDcsIiIsMSx7InN0eWxlIjp7ImhlYWQiOnsibmFtZSI6ImVwaSJ9fX1dLFsyLDhdXQ==
    #align(center, diagram({
      node((-2, -1), [$dots.c$])
      node((-1, -1), [$Pic(X)$])
      node((0, -1), [$H^2 (X, mu_n)$])
      node((1, -1), [$H^2 (X, GG_m)$])
      node((2, -1), [$dots.c$])
      node((1, 0), [$0$])
      node((-2, 0), [$dots.c$])
      node((-1, 0), [$Pic(X_0)$])
      node((0, 0), [$H^2 (X_0, mu_n)$])
      edge((-2, -1), (-1, -1), "->")
      edge((-1, -1), (0, -1), "->")
      edge((0, -1), (1, -1), "->")
      edge((1, -1), (2, -1), "->")
      edge((-2, 0), (-1, 0), "->")
      edge((-1, 0), (0, 0), "->>")
      edge((0, 0), (1, 0), "->")
      edge((-1, -1), (-1, 0), "->>")
      edge((0, -1), (0, 0), "->")
    }))
    于是限制映射 $H^2 (X, mu_n) -> H^2 (X_0, mu_n)$ 是满射，证毕。 

  - $q >= 3$ 的情形：由 @pbc-seed-precursor-3，$H^q (X_0, ul(ZZ\/n)) = 0$，故限制映射 $H^q (X, ul(ZZ\/n)) -> H^q (X_0, ul(ZZ\/n))$ 自动是满射。 
]

既然 (Seed) 已经验证，紧合基变换定理证明中的每一步就都建立起来了。于是我们完整证明了紧合基变换定理（@proper-base-change，除局部 Noether 这一假设之外）： 

- 考虑一个拉回图表：#h(1fr)
  // https://q.uiver.app/#r=typst&q=WzAsNCxbMCwwLCJYJyJdLFsxLDAsIlknIl0sWzAsMSwiWCJdLFsxLDEsIlkiXSxbMiwzLCJmIl0sWzAsMSwiZiciXSxbMSwzLCJnIl0sWzAsMiwiZyciLDJdXQ==
  #align(center, diagram({
    node((-1, -1), [$X'$])
    node((0, -1), [$Y'$])
    node((-1, 0), [$X$])
    node((0, 0), [$Y$])
    node((-0.7, -0.7), $cart$)
    edge((-1, 0), (0, 0), [$f$], label-side: left, "->")
    edge((-1, -1), (0, -1), [$f'$], label-side: left, "->")
    edge((0, -1), (0, 0), [$g$], label-side: left, "->")
    edge((-1, -1), (-1, 0), [$g'$], label-side: right, "->")
  }))
  若 $f$ 紧合，且 $Y, Y'$ 局部 Noether，则对所有挠层 $cal(F) in cAb(X_et)$，基变换态射： 
  $
    g^(-1) R^q f_* cal(F) -> R^q f'_* g'^(-1) cal(F)
  $
  是同构。 
