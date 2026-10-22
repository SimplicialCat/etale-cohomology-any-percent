#import "void-import.typ": *

本附录证明 Artin 逼近定理，它是紧合基变换定理的证明所依赖的关键一环。定理的表述如下： 

- 设 $A$ 是某个有限型代数在某个素理想处的 Hensel 化，而这个代数定义在某个域或某个优良离散赋值环上，$hat(A)$ 是 $A$ 关于其极大理想 $frak(m)$ 的完备化。 

  给定多项式方程组 $f_1, dots.c, f_m in A[Y_1, dots.c, Y_n]$，假设存在形式解 $hat(a)_1, dots.c, hat(a)_n in hat(A)$，即： 
  $
    f_1 (hat(a)_1, dots.c, hat(a)_n) = dots.c = f_m (hat(a)_1, dots.c, hat(a)_n) = 0
  $
  则对每个 $N >= 1$，存在真正的解 $a_1, dots.c, a_n in A$，使得： 
  $
    f_1 (a_1, dots.c, a_n) = dots.c = f_m (a_1, dots.c, a_n) = 0
  $
  且每个 $hat(a)_i equiv a_i (mod frak(m)^N)$。 

我们采用 @cite-Art69 的证明方法，而不用 Stacks Project 基于 Popescu 定理给出的更现代的证明。这样做是为了让这份证明尽可能少依赖外部结果。证明本身十分冗长、技术性很强，因此我们把本附录分成三节。

== 预备化归

#notation[
  设 $(A, frak(m))$ 是 Noether 的 Hensel 局部环。若对每个多项式方程组 $f_1, dots.c, f_m in A[Y_1, dots.c, Y_n]$，只要它有形式解 $hat(a)_1, dots.c, hat(a)_n in hat(A)$，即： 
  $
    f_1 (hat(a)_1, dots.c, hat(a)_n) = dots.c = f_m (hat(a)_1, dots.c, hat(a)_n) = 0
  $
  就对每个 $N >= 1$ 都存在真正的解 $a_1, dots.c, a_n in A$，使得： 
  $
    f_1 (a_1, dots.c, a_n) = dots.c = f_m (a_1, dots.c, a_n) = 0
  $
  且每个 $hat(a)_i equiv a_i (mod frak(m)^N)$，则称 *Artin 逼近*在 $A$ 上成立。 
]

#notation[
  对局部环 $(A, frak(m))$，我们记： 
  $
    A{T_1, dots.c, T_n} = A[T_1, dots.c, T_n]_((frak(m),T_1,dots.c,T_n))^#[h]
  $
]

#proposition(name: <artin-approx-and-finitely-presented-functors>)[
  设 $(A, frak(m))$ 是 Noether 局部环。以下条件等价： 

  + Artin 逼近在 $A$ 上成立； 

  + 对任意与正向极限交换的函子 $F: AAlg(A) -> cSet$，任意 $N >= 1$，以及任意元素 $hat(xi) in F(hat(A))$，都存在元素 $xi in F(A)$，使得 $hat(xi)$ 与 $xi$ 在 $F(A\/frak(m)^N)$ 中的像相同。 
]
#proof[
  ($==>$) 把 $hat(A) = dirlim_lambda A_lambda$ 写成其有限型 $A$-子代数的正向极限。于是： 
  $
    F(hat(A)) = dirlim_lambda F(A_lambda)
  $
  设 $hat(xi) in F(hat(A))$，其中 $xi_lambda in F(A_lambda)$ 是 $hat(xi)$ 的一个代表元。 

  设 $A_lambda$ 有展示 $A[Y_1,dots.c,Y_m]\/(f_1,dots.c,f_r)$。于是包含映射 $A_lambda -> hat(A)$ 给出 $arrow(f)(arrow(Y)) = 0$ 的一个形式解 $hat(a) in hat(A)^m$。于是存在解 $a in A^m$，它在模 $frak(m)^N$ 下与 $hat(a)$ 一致。换言之，我们得到结构映射的一个截面： 
  $
    phi: A_lambda -> A
  $
  它在模 $frak(m)^N$ 约化后与 $A_lambda -> hat(A)$ 一致。 

  令 $xi = F(phi) xi_lambda in F(A)$。则 $hat(xi)$ 与 $xi$ 在模 $frak(m)^N$ 约化后一致。 

  ($<==$) 
  #notation[
    对多项式方程组 $f_1, dots.c, f_r in A[Y_1,dots.c,Y_m]$，我们定义解函子 (solution functor)：
    $
      F_(arrow(f)): AAlg(A) &-> cSet \
      B &|-> {arrow(b) in B^m : arrow(f)(arrow(b)) = 0}
    $
  ]
  直接验证可知 $F_(arrow(f))$ 与正向极限交换。因此 $arrow(f)$ 的形式解都可以被逼近。  
]

#proposition(name: <artin-approx-reduce-to-std>)[
  以下条件等价： 

  + 任一域上或任一优良离散赋值环 $R$ 上的有限型代数 $A$，其在任意素理想处的 Hensel 化都满足 Artin 逼近； 

  + 对任意优良离散赋值环 $R$，令 $A = R{X_1, dots.c, X_n}$。对任意 $N >= 1$，若多项式方程组 $f_1, dots.c, f_r in R[Y_1, dots.c, Y_m]$ 有形式解 $hat(a)_1, dots.c, hat(a)_m in hat(A)$，其中 $hat(A) = hat(R) fps(X_1\, dots.c\, X_n)$： 
    $
      f_1 (hat(a)_1, dots.c, hat(a)_m) = dots.c = f_r (hat(a)_1, dots.c, hat(a)_m) = 0
    $
    则存在解 $a_1, dots.c, a_m in A$，它满足下面的方程组，且与 $hat(a)_1, dots.c, hat(a)_m in hat(A)$ 在模 $frak(m)_A^N$ 下一致： 
    $
      f_1 (a_1, dots.c, a_m) = dots.c = f_r (a_1, dots.c, a_m) = 0
    $

    也就是说，环 $R{X_1, dots.c, X_n}$ 上的 Artin 逼近对 $R[X_1,dots.c,X_n,Y_1,dots.c,Y_m]$ 中的多项式方程组（即 $R[X_1,dots.c,X_n]$ 上的方程组）成立。 
]
#proof[
  (1) $==>$(2) 是形式上的（无需实质论证），故只需证明 (2) $==>$(1)。 

  若 $R$ 是离散赋值环，且 $frak(m)_A in Spec(A)$ 位于 $Spec(R)$ 的泛点上方，则可用 $Frac(R)$ 替换 $R$。此时若 $R$ 是域，则用 $R fps(T)$ 替换 $R$，并让 $T$ 在 $A$ 上作用为零。经过这些化归，不妨设 $R$ 是离散赋值环，且 $A$ 位于 $R$ 的闭点 $(pi.alt)$ 上方。 

  接下来我们断言，不妨设 $k(A)\/k(R)$ 是有限域扩张。事实上： 
  
  - 假定这一情形已经解决，我们再把一般情形化归到它。$k(A)\/k(R)$ 是有限生成域扩张，故可取 $z_1, dots.c, z_d in A$，使其在 $k(A)$ 中的剩余类构成 $k(A)\/k(R)$ 的一组超越基。它们诱导出局部映射： 
    $
      R[T_1,dots.c,T_d]_((pi.alt)) -> A, T_i |-> z_i
    $
    （这个映射是良定义的。事实上，对任意不被 $pi.alt$ 整除的多项式 $f(T_1,dots.c,T_d) in R[T_1,dots.c,T_d]$，$[f(z_1, dots.c, z_d)] in k(A)$ 是 $[z_1], dot.c, [z_d]$ 的非零多项式。由代数无关性，$[f(z_1, dots.c, z_d)] in k(A)^times$。）

    于是 $A$ 是 $R' = R[T_1,dots.c,T_d]_((pi.alt))$ 上的 Hensel 局部环。由于 $A$ 是某个有限型 $R$-代数在某个素理想处的 Hensel 化，它也是某个有限型 $R'$-代数在某个素理想处的 Hensel 化。$R'$ 是优良离散赋值环，故可用 $R'$ 替换 $R$。现在，$k(A)$ 在 $k(R') = k(R)(z_1, dots.c, z_d)$ 上的剩余域扩张是有限的。 

  现在取有限型 $R$-代数 $C_0$ 与 $frak(m)_0 in Spec(C_0)$，使得 $A = C_(0,frak(m)_0)^#[h]$。$frak(m)_0$ 必定位于 $(pi.alt) in Spec(R)$ 上方。由于剩余域 $k(A) = k(C_0)$ 在 $k(R)$ 上有限，由 Hilbert 零点定理，$frak(m)_0$ 是 $Spec(C_0\/pi.alt C_0)$ 的闭点，从而是 $C_0$ 的极大理想。 

  取定一组生成元，使 $C_0 = R[z_1, dots.c, z_n]$。每个 $[z_i] in k(C_0)$ 都满足 $k(R)$ 上的某个首一多项式关系。把这个关系任意提升为 $P_i [T] in R[T]$，使得 $x_i = P_i (z_i) in frak(m)_0$。定义映射： 
  $
    R[X_1,dots.c,X_n] -> C_0, X_i |-> x_i
  $
  于是每个生成元 $z_i in C_0$ 都满足 $P_i (z_i) = x_i$，故 $C_0$ 在 $R[X_1,dots.c,X_n]$ 上是整的，从而是有限的。此外，$frak(m)_0$ 的原像包含极大理想 $(pi.alt, X_1, dots.c, X_n)$，因为 $pi.alt in frak(m)_0$ 且 $x_i in frak(m)_0$。于是 $frak(m)_0$ 位于 $(pi.alt, X_1, dots.c, X_n)$ 上方，给出有限映射： 
  $
    R[X_1,dots.c,X_n]_((pi.alt, X_1, dots.c, X_n)) -> C_(0,frak(m)_0)
  $
  由 @henselization-and-finite-base-change，$A = C_(0,frak(m)_0)^#[h]$ 是 $C_0 otimes_(R[X_1,dots.c,X_n]) R{X_1,dots.c,X_n}$ 的一个因子。因此 $A$ 是 $R{X_1,dots.c,X_n}$ 上的有限局部代数。 

  #notation[
    在本附录余下的部分中，我们始终记： 
    $
      A_n := R{X_1, dots.c, X_n}
    $
    其中 $R$ 是上下文中明确的优良离散赋值环。记 $frak(m)_n = (pi.alt, X_1, dots.c, X_n) A_n$ 为 $A_n$ 的极大理想。 
  ]

  现在 $A\/frak(m)_n A$ 是域 $k(R)$ 上的有限局部代数，从而是局部 Artin 环。这说明 $sqrt(frak(m)_n A) = frak(m)_A$，因此 $A$ 上的 $frak(m)_n A$-进拓扑与 $frak(m)_A$-进拓扑等价。换言之， 
  $
    hat(A) cong A otimes_(A_n) hat(A_n)
  $
  接下来，对每个多项式方程组 $f_1, dots.c, f_r in A[Y_1,dots.c,Y_m]$，定义函子： 
  $
    G: AAlg(A_n) -> cSet, B |-> F_(arrow(f)) (A otimes_(A_n) B)
  $
  这个函子与正向极限交换，因为 $F_(arrow(f))$ 与张量积都与正向极限交换。若假定 Artin 逼近对 $A_n$ 成立，则 $G(hat(A_n))$ 中的点都可由 $G(A_n)$ 中的点逼近。也就是说，$F_(arrow(f)) (hat(A))$ 中的点都可由 $F_(arrow(f)) (A)$ 中的点逼近。换言之，$arrow(f)$ 的形式解都可以被逼近。 

  总之，只需对环 $A_n$ 证明 Artin 逼近。我们已经假定过：对环 $A_n$、对定义在 $R[X_1,dots.c,X_n]$ 上的那些方程组，Artin 逼近成立，故只需化归到这类方程组。 

  设 $f_1,dots.c,f_r in A_n [Y_1,dots.c,Y_m]$ 是 $A_n$ 上的一个方程组，并设它有解 $hat(y) in hat(A_n)$。把方程组扩大，使 $(f_1,dots.c,f_r)$ 生成下述理想： 
  $
    frak(p) = ker(A_n [arrow(Y)], Y_i |-> hat(y)_i) in Spec(A_n [arrow(Y)])
  $
  令 $B_n = R[X_1,dots.c,X_n]_((pi.alt,X_1,dots.c,X_n))$，于是 $A_n = B_n^#[h]$。令 $frak(p)_0 = frak(p) inter B_n [arrow(Y)] in Spec(B_n [arrow(Y)])$。现在： 

  - $A_n [arrow(Y)]\/frak(p)_0 A_n [arrow(Y)]$ 是一族平展 $B_n [arrow(Y)]\/frak(p)_0$-代数的滤余极限，而由 @etale-local-properties (4)，其中每个代数都既约。因此 $A_n [arrow(Y)]\/frak(p)_0 A_n [arrow(Y)]$ 既约。 

    也就是说，$frak(p)_0 A_n [arrow(Y)]$ 是 $A_n [arrow(Y)]$ 的根理想。 

  - $frak(p)$ 是 $A_n [arrow(Y)]$ 中位于 $frak(p)_0 A_n [arrow(Y)]$ 上方的极小素理想之一。事实上，映射 $Spec(A_n [arrow(Y)]) -> Spec(B_n [arrow(Y)])$ 是仿射平展映射的逆向极限。于是它在 $frak(p)_0$ 上的纤维是离散集，所以 $frak(p)_0$ 上方的素理想都不能真特殊化到 $frak(p)$。 

  设 $frak(q)_1 = frak(p), dots.c, frak(q)_e in Spec(A_n [arrow(Y)])$ 是 $frak(p)_0 A_n [arrow(Y)]$ 上方的极小素理想。于是由 $frak(p)_0 A_n [arrow(Y)]$ 是根理想可得： 
  $
    frak(p)_0 A_n [arrow(Y)] = frak(p) inter frak(q)_2 inter dots.c inter frak(q)_e
  $
  对 $2<=i<=e$ 取 $g_i in frak(q)_i - frak(p)$。令 $g = product_(i=2)^e g_i in frak(q)_2 dots.c frak(q)_e - frak(p)$。则： 

  - $g(hat(y)) != 0$，这是因为 $g in.not frak(p)$； 

  - $g frak(p) subset frak(p) frak(q)_2 dots.c frak(q)_e subset frak(p)_0 A_n [arrow(Y)]$。 

  取 $frak(p)_0 subset B_n [arrow(Y)]$ 的一组生成元，并把它们的分母消去（这些分母都是 $R[arrow(X)] - (pi.alt, arrow(X))$ 中的元素）。于是有多项式 $phi_1, dots.c, phi_t in R[arrow(X), arrow(Y)]$，使得 $frak(p)_0 = (phi_1, dots.c, phi_t)$。则： 

  - $arrow(phi)(hat(y)) = 0$，故由 $R[arrow(X), arrow(Y)]$ 中方程组的逼近性，对充分大的 $N$，可以取到模 $frak(m)_n^N$ 的逼近 $y in A_n^m$。 

  - 只要 $N > "ord"_(frak(m)_n) (g(hat(y)))$，就有 $0 != g(hat(y)) mod frak(m)_n^N = g(y) mod frak(m)_n^N$，从而 $g(y) != 0$。 

  现在对原来的每个方程 $f_i$，都有 $g f_i in frak(p)_0 A_n [arrow(Y)]$，故 $g(y) f_i (y) = 0$。但 $g(y) != 0$，所以 $f_i (y) = 0$。这样我们就得到了 $hat(y)$ 的一个逼近解 $y in A_n^m$。 
]
