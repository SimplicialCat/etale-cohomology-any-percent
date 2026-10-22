#import "void-import.typ": *
== 挠层

本节我们引入挠层的概念，并建立一些初步性质。 

#definition(name: <defn-torsion-sheaf>)[
  若交换群层 $cal(F) in cAb(X_et)$ 满足：
  $
    cal(F) = dirlim_(n>=1) cal(F)[n!]
  $
  则称它为*挠层*，其中 $cal(F)[n!]$ 表示 $cal(F)$ 的 $n!$-挠子层。 
]

#proposition(name: <torsion-sheaves-first-props>)[
  给定 $cal(F) in cAb(X_et)$，以下条件等价： 

  + $cal(F)$ 是挠层； 

  + 对任意 $U in Et_X$ 与任意截面 $s in cal(F)(U)$，都存在平展覆盖 $cal(U) = {U_i -> U}_i$，使得每个 $s|_(U_i)$ 都是 $cal(F)(U_i)$ 中的挠元； 

  + 对 $X$ 的任意几何点 $ol(x)$，$cal(F)_(ol(x))$ 是挠交换群。 
]
#proof[
  (1) $==>$(2)：令 $cal(P) = dirlim_(n>=1,cPAb) cal(F)[n!]$ 为 $cal(F)$ 中由挠截面组成的子预层。于是由挠交换群层的定义以及 @ab-x-et-the-abelian-cat 的 (3)，有 
  $
    cal(P)^\# = cal(F)
  $
  由于 $cal(P)$ 是层 $cal(F)$ 的子预层，故为分离预层，于是 $cal(P)^\# = cal(P)^+$。因此 
  $
    cal(F)(U) = dirlim_(cal(U) = {U_i -> U}_i) ker(product_i cal(P)(U_i) -> product_(i,j) cal(P)(U_i times_U U_j))
  $
  从而每个截面 $s in cal(F)(U)$ 都有平展覆盖 $cal(U) = {U_i -> U}_i$，使得每个 $s|_(U_i) in cal(P)(U_i)$ 都成立。证毕。 

  (2) $==>$(3)：回忆： 
  $
    cal(F)_(ol(x)) = dircolim_((U,ol(u)) -> (X,ol(x)) #[etale]) cal(F)(U)
  $
  现在每个 $[s] in cal(F)_(ol(x))$ 都由某个 $s in cal(F)(U)$ 代表。由 (b)，存在平展态射 $(V, ol(v)) -> (U, ol(u))$，使得 $s|_V in cal(F)(V)$ 是挠元，即有 $n(s|_V) = 0$。换言之，$n[s] = n[s|_V] = [n(s|_V)] = 0 in cal(F)_(ol(x))$，证毕。 

  (3) $==>$(1)：取茎是左伴随，故与余极限交换；其中末一等号成立，是因为 $cal(F)_(ol(x))$ 是挠交换群： 
  $
    (dirlim_(n>=1) cal(F)[n!])_(ol(x)) = dirlim_(n>=1) cal(F)_(ol(x))[n!] = cal(F)_(ol(x))
  $
  再由 @stalks-detects-properties 即得 
  $
    dirlim_(n>=1) cal(F)[n!] = cal(F)
  $
]

#corollary(name: <pullback-of-torsion-sheaf>)[
  给定任意概形态射 $f: X -> Y$ 与任意挠层 $cal(G) in cAb(Y_et)$，$f^(-1) cal(G)$ 是挠层。 
]
#proof[
  我们使用 @torsion-sheaves-first-props 的等价条件 (c)，并观察到，对每个几何点 $ol(x)$，都有 $(f^(-1) cal(G))_(ol(x)) = cal(G)_(f(ol(x)))$，右边是挠交换群。 
]

我们还需要简短讨论一下固定 $n>=1$ 时的 $n$-挠层范畴；这一讨论最终会用在紧合基变换的证明中。 

#definition(name: <defn-zn-module-sheaf>)[
  给定自然数 $n>=1$，若交换群预层/层 $cal(F)$ 是 $n$-挠的，则称它为 *$ZZ\/n$-模预层/层*。 
  
  $X$ 上 $ZZ\/n$-模的预层/层范畴，记作 $cPAb(X_et, ZZ\/n)$ 与 $cAb(X_et, ZZ\/n)$，是 $cPAb(X_et)$ 与 $cAb(X_et)$ 中由 $ZZ\/n$-模预层/层组成的满子范畴。 
]

#properties(name: <etale-zn-sheaves-first-props>)[
  + 平展层/预层范畴之间的任意加性函子都保持 $ZZ\/n$-模子范畴。 
    
    特别地，函子 $R^q f_*, f^(-1)_cPSh, f^(-1), (-)^\#, f_!, i^!$ 都保持 $ZZ\/n$-模子范畴。 
  
  + $cAb(X_et, ZZ\/n)$ 是 Abel 范畴，满足 (Ab5)，且有足够多的内射对象。 
  
  + 对任意 $U in Et_X$ 与任意 $f: X -> Y$，任意内射对象 $cal(I) in cAb(X_et, ZZ\/n)$ 关于 $Gamma(U, -)$ 与 $f_*$ 都零调。 
]
#proof[
  (1) 任意加性函子都把态射 $times n$ 送到 $times n$，因此保持那些 $times n$ 在其上为零态射的对象。 
  
  (2) 除“有足够多的内射对象”外，其余各条都由 $cAb(X_et)$ 上对应的性质得到。现在考虑 $n$-挠函子：
  $
    [n]: cAb(X_et) -> cAb(X_et, ZZ\/n), cal(F) |-> cal(F)[n]
  $
  它把一个层送到这个层的 $n$-挠部分。现在对任意 $cal(G) in cAb(X_et, ZZ\/n)$，有 
  $
    Hom_cAb (cal(G), cal(F)) = Hom_cAb (cal(G), cal(F)[n])
  $
  由于 $cal(G)$ 是 $n$-挠的，任一从它出发的态射的像都仍是 $n$-挠的。换言之，遗忘函子 $cAb(X_et, ZZ\/n) -> cAb(X_et)$ 是 $[n]$ 的左伴随。由于这个左伴随正合，$[n]$ 保持内射对象。 
  
  现在对任意 $cal(G) in cAb(X_et, ZZ\/n)$，都有嵌入 $cal(G) arrow.hook cal(I)$，其中 $cal(I) in cAb(X_et)$ 是内射对象。于是有嵌入 $cal(G) arrow.hook cal(I)[n]$，它落在 $cal(I)$ 的 $n$-挠部分中，而 $cal(I)[n] in cAb(X_et, ZZ\/n)$ 是内射对象。 
  
  (3) 取内射对象 $cal(J) in cAb(X_et)$ 及嵌入 $cal(I) arrow.hook cal(J)$。由于 $cal(I)$ 是 $n$-挠的，在 $cAb(X_et, ZZ\/n)$ 中有嵌入 $cal(I) arrow.hook cal(J)[n]$。又因 $cal(I) in cAb(X_et, ZZ\/n)$ 是内射对象，故 $cal(I)$ 是 $cal(J)[n]$ 的直和项。于是只需证明 $cal(J)[n]$ 零调。 
  
  由于 $cal(J)$ 是内射平展层，且对任意 $U in Et_X$，$times n: ul(ZZ)_(!,U) -> ul(ZZ)_(!,U)$ 都是单射，所以 $times n: cal(J)(U) -> cal(J)(U)$ 必为满射。换言之，$times n: cal(J) -> cal(J)$ 是满射，于是得到 $cal(J)[n]$ 的一个内射消解： 
  $
    0 -> cal(J)[n] -> cal(J) ->^(times n) cal(J) -> 0
  $
  这样一来，对任意定义在 $cAb(X_et)$ 上的左正合加性函子 $F$（例如 $Gamma(U, -)$ 或 $f_*$），都有 $R^q F (cal(J)[n]) = 0$（$q >= 2$）以及 $R^1 F(cal(J)[n]) = coker(times n: F(cal(J)) -> F(cal(J)))$。因此当 $q >= 2$ 时自动有 $H^q (U, cal(J)[n]) = 0$ 与 $R^q f_* (cal(J)[n]) = 0$。至于 $q = 1$， 
  $
    H^1 (U, cal(J)[n]) = coker(times n: cal(J)(U) -> cal(J)(U)) = 0
  $
  正如上文所验证的。又因 $times n: f_* cal(J) -> f_* cal(J)$ 逐截面看就是 $cal(J)$ 截面上的 $times n$，它同样为满射。因此 $R^1 f_* (cal(J)[n]) = 0$。证毕。 
]
