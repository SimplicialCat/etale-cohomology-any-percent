#import "void-import.typ": *

本附录证明几个辅助结果，刻画严格 Hensel 化与拟有限映射之间的相互作用。这些结果在局部零调性理论中会非常有用。 

本附录的论述大体沿用 #cite-stacks("0GIN")[Section 10.156]。 

#lemma(name: <strict-hs-and-qfinite>)[
  (#cite-stacks("05WR")[Lemma 10.156.3]) 设 $A -> B$ 是环同态，而 $frak(q) in Spec(B)$ 位于 $frak(p) in Spec(A)$ 之上。假设 $Spec(B) -> Spec(A)$ 在 $frak(q)$ 处拟有限。取定可分闭包 $k(frak(q)) arrow.r.hook k(frak(q))^sep$，并令 $k(frak(p))^sep$ 为 $k(frak(p))$ 在 $k(frak(q))^sep$ 中的可分闭包。严格 Hensel 化都关于这些可分闭包来取。 
  
  令： 
  $
    frak(r) = ker(A_(frak(p))^#[sh] otimes_(A_(frak(p))) B_(frak(q)) -> k(frak(p))^sep otimes_(k(frak(p))) k(frak(q)) -> k(frak(q))^sep)
  $
  则存在典范同构： 
  $
    (A_(frak(p))^#[sh] otimes_(A_(frak(p))) B_(frak(q)))_(frak(r)) cong B_(frak(q))^#[sh]
  $
  且 $A_(frak(p))^#[sh] -> B_(frak(q))^#[sh]$ 有限。 
]
#proof[
  由在 $frak(q)$ 处的拟有限性可知，$k(frak(q))\/k(frak(p))$ 是有限扩张。于是 $k(frak(p))^sep$ 是 $k(frak(p))$ 的可分闭包。 
  
  此外，合成域 $k(frak(q)) k(frak(p))^sep subset k(frak(q))^sep$ 在可分闭域 $k(frak(p))^sep$ 上有限，从而是纯不可分的。因此它是可分闭的。又因它在 $k(frak(q))$ 上可分，故等于 $k(frak(q))^sep$。于是 $k(frak(q))^sep\/k(frak(p))^sep$ 有限且纯不可分，而映射 
  $
    k(frak(p))^sep otimes_(k(frak(p))) k(frak(q)) -> k(frak(q))^sep
  $
  是满射。

  令 $R = A_(frak(p))^#[sh]$，$C = R otimes_(A_(frak(p))) B_(frak(q))$。拟有限性在基变换下保持，故 $C$ 在 $frak(r)$ 处是 $R$ 上拟有限的。由 Zariski 主定理，$frak(r)$ 的开邻域 $U subset Spec(C)$ 可经一个开浸入嵌入到某个在 $Spec(R)$ 上有限的概形 $ol(U)$ 中。 
  
  由于 $R$ 是 Hensel 的，由 @equiv-defns-of-henselian (1)，$ol(U)$ 分解为有限局部 $R$-代数的谱。点 $frak(r)$ 是其中一个分支 $V$ 的闭点。此时 $U inter V$ 含有局部概形 $V$ 的闭点，故 $U inter V = V$。于是
  $
    C_(frak(r)) cong cal(O)_(V,frak(r))
  $
  是一个有限局部 $R$-代数。因此由 @finite-over-henselian-is-henselian，它是严格 Hensel 的。由 $k(frak(p))^sep otimes_(k(frak(p))) k(frak(q)) -> k(frak(q))^sep$ 的满射性，$C_(frak(r))$ 的剩余域是 $k(frak(q))^sep$，故 $C_(frak(r))$ 是严格 Hensel 的。

  局部映射 $B_(frak(q)) -> C_(frak(r))$ 与所选定的剩余域嵌入相容，故由严格 Hensel 化的泛性质，得到唯一的局部映射： 
  $
    B_(frak(q))^#[sh] -> C_(frak(r))
  $
  反之，相容的映射 $R -> B_(frak(q))^#[sh]$ 与 $B_(frak(q)) -> B_(frak(q))^#[sh]$ 诱导出映射 $C -> B_(frak(q))^#[sh]$。由 $frak(r)$ 的定义，极大理想的逆像是 $frak(r)$，故这个映射局部化为： 
  $
    C_(frak(r)) -> B_(frak(q))^#[sh].
  $
  由严格 Hensel 化泛性质中的唯一性，这两个映射的复合在 $B_(frak(q))^#[sh]$ 上是恒等映射。它们在 $C_(frak(r))$ 上的复合也是恒等映射，因为它是从 $C$ 的局部化到自身的 $C$-代数映射。于是这两个映射互为逆映射，都是典范同构。最后，$A_(frak(p))^#[sh] -> B_(frak(q))^#[sh]$ 有限，因为如上所论，$C_(frak(r))$ 在 $R$ 上有限。 
]

#lemma(name: <tensor-of-local-rings-still-local-criterion>)[
  (#cite-stacks("092Y")[Lemma 10.156.5]) 设 $A -> B$ 与 $A -> C$ 是局部环之间的局部同态，使得： 

  - $A -> C$ 是整的； 

  - $k(B)\/k(A)$ 与 $k(C)\/k(A)$ 中至少有一个是纯不可分的。 

  则 $D = B otimes_A C$ 是局部环，且 $B -> D$、$C -> D$ 都是局部同态。 
]
#proof[
  注意：
  $
    D\/frak(m)_B D cong k(B) otimes_A C cong k(B) otimes_(k(A)) C\/frak(m)_A C
  $
  由于 $C$ 是局部环且在 $A$ 上整，$Spec(C\/frak(m)_A C)$ 是局部概形，且在域 $k(A)$ 上整。由上行性质，它是 $0$ 维的，于是只有一个点 $frak(m)_C\/frak(m)_A C$。 
  
  于是 $k(C) = (C\/frak(m)_A C)_#[red]$，从而 $Spec(D\/frak(m)_B D)$ 同胚于 $Spec(k(B) otimes_(k(A)) k(C))$。由于 $k(B)\/k(A)$ 与 $k(C)\/k(A)$ 之一纯不可分，$Spec(k(B) otimes_(k(A)) k(C))$ 只有一个点。因此 $Spec(D\/frak(m)_B D)$ 只有一个点。 

  映射 $B -> D$ 是整映射 $A -> C$ 的基变换，故是整的。于是由上行性质，$D$ 的每个极大理想都位于 $frak(m)_B$ 之上。但 $Spec(D\/frak(m)_B D)$ 只有一个点。因此 $D$ 只有一个极大理想，所以 $D$ 是局部环，且 $frak(m)_D$ 位于 $frak(m)_B$ 之上。此外 $D\/frak(m)_B D cong k(B) otimes_(k(A)) C\/frak(m)_A C$，其中左端的谱只有点 $frak(m)_D$，右端的谱只有点 $frak(m)_C$。于是 $frak(m)_D$ 位于 $frak(m)_C$ 之上，从而 $B -> D$ 与 $C -> D$ 都是局部同态。 
]

#lemma(name: <strict-henselizations-tensors-and-qfinites>)[
  设 $B, C$ 是 $A$-代数，$D = B otimes_A C$，$Omega$ 是某个可分闭域。给定环同态 $psi_D: D -> Omega$，与结构映射复合，便分别得到从 $A,B,C$ 到 $Omega$ 的同态 $psi_A, psi_B, psi_C$。分别令 $frak(p)_(A,B,C,D)$ 为 $ker(psi_(A,B,C,D))$，它们是对应环的素理想。这些理想一个位于另一个之上。当 $B_(frak(p)_B)$ 是拟有限 $A_(frak(p)_A)$-代数的滤余极限时，典范映射 
  $
    B_(frak(p)_B)^#[sh] otimes_(A_(frak(p)_A)^#[sh]) C_(frak(p)_C)^#[sh] -> D_(frak(p)_D)^#[sh]
  $
  是同构。这包括以下情形： 

  - $A -> B$ 在 $frak(p)_B$ 处拟有限；
  
  - $B$ 是拟有限 $A$-代数的滤余极限。特别地，$B$ 在 $A$ 上整时就属于这种情形。 

  （这里 $A,B,C,D$ 的严格 Hensel 化都是相对于 $k(frak(p)_(A,B,C,D))$ 在 $Omega$ 中的可分闭包来取的。）
]
#proof[
  把 $A, B, C$ 分别换成 $A_(frak(p)_A), B_(frak(p)_B), C_(frak(p)_C)$，便可假设 $A, B, C$ 都是局部环，结构映射 $A -> B, A -> C$ 是局部同态，且 $frak(p)_(A,B,C) = frak(m)_(A,B,C)$。 

  严格 Hensel 化与滤余极限相容（@henselization-and-directed-limits，另见 @artin-mazur-construction），张量积与滤余极限也相容，故不妨假设 $B$ 是拟有限 $A$-代数。 

  考虑典范映射： 
  $
    B^#[sh] otimes_(A^#[sh]) C^#[sh] -> D_(frak(p)_D)^#[sh]
  $
  因 $B$ 在 $A$ 上拟有限，由 @strict-hs-and-qfinite 有 
  $
    B^#[sh] cong (A^#[sh] otimes_A B)_(ker(A^#[sh] otimes_A B -> Omega))
  $
  而 $D$ 经基变换在 $C$ 上拟有限，同样由 @strict-hs-and-qfinite 有 
  $
    D_(frak(p)_D)^#[sh] cong (C^#[sh] otimes_C D)_(ker(C^#[sh] otimes_C D -> Omega))
  $
  按定义，$C^#[sh] otimes_C D cong C^#[sh] otimes_A B$。于是 
  $
    B^#[sh] otimes_(A^#[sh]) C^#[sh] cong (C^#[sh] otimes_A B)_(ker(A^#[sh] otimes_A B -> Omega))
  $
  从而典范同态 $B^#[sh] otimes_(A^#[sh]) C^#[sh] -> D_(frak(p)_D)^#[sh]$ 的两端都是同一个环 $C^#[sh] otimes_A B$ 的局部化，且彼此相容。要证明它是同构，只需证明两端都是局部环。 
  
  因此只需证明 $B^#[sh] otimes_(A^#[sh]) C^#[sh]$ 是局部环。由 @strict-hs-and-qfinite，$A^#[sh] -> B^#[sh]$ 有限，且剩余域扩张纯不可分。于是由 @tensor-of-local-rings-still-local-criterion，$B^#[sh] otimes_(A^#[sh]) C^#[sh]$ 是局部环，证毕。 
]
