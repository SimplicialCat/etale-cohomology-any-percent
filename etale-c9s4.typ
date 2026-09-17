#import "void-import.typ": *
== Verdier duality

In this section, we establish so-called Verdier duality, a result on the dualizability of complexes of etale sheaves. This will be our final puzzle piece in the theory of etale cohomology. 

The method of this section closely follows that of @cite-lei-fu[Section 9.6], with specialization to the case where the base is a field. The finiteness and biduality arguments in @cite-lei-fu also works over a regular $1$-dimensional base, so you should check it out if you want more general results. 

#definition(name: <defn-dualizing-complex-functor>)[
  Let $f: X -> Spec(k)$ be a separated morphism of finite type, where $k$ is a field and $Lambda$ is an $n$-torsion noetherian ring s.t. $n in k^times$. Then we define *the dualizing complex* functor to be the contravariant functor: 
  $
    DD_X = DD_(X\/k): D^b_#[ctf] (X_et, Lambda)^opp &-> D^b_#[ctf] (X_et, Lambda) \
    
    cal(K) &|-> RHHom_Lambda (cal(K), R f^! Lambda)
  $
  Here, the preservation of $D^b_#[ctf]$ follows from @finiteness-of-six-functors, finiteness of six functors. 

  Now by definition, there is a $Lambda$-bilinear evaluation pairing: 
  $
    cal(K) Lotimes_Lambda RHHom_Lambda (cal(K), R f^! Lambda) -> R f^! Lambda
  $
  inducing a natural map $cal(K) -> DD_X DD_X cal(K)$ by adjunction. 
]

The statement of biduality is that the natural map $cal(K) -> DD_X DD_X cal(K)$ is always an isomorphism. 

#lemma[
  The biduality map $cal(K) -> DD_X DD_X cal(K)$ is an isomorphism for all $cal(K) in D^b_#[ctf] (X_et, Lambda)$, whenever $X = Spec(k)$ itself and $k$ is separably closed. 
]
#proof[
  This is to show that for any complex $M^bullet$ of finite flat $Lambda$-modules, 
  $
    M^bullet -> RHom_Lambda (RHom_Lambda (M^bullet, Lambda), Lambda)
  $
  is an isomorphism. Indeed, each $M^q$ is finite flat over the noetherian ring $Lambda$, hence projective and locally free. Thus the map $M^bullet -> RHom_Lambda (RHom_Lambda (M^bullet, Lambda), Lambda)$ is defined termwise by: 
  $
    M^q -> Hom_Lambda (Hom_Lambda (M^q, Lambda), Lambda)
  $
  Since $M^q$ is finite locally free, this map is an isomorphism. 
]

#lemma(name: <partial-biduality-in-proper-case>)[
  The biduality map $cal(K) -> DD_X DD_X cal(K)$ is an isomorphism for all $cal(K) in D^b_#[ctf] (X_et, Lambda)$ after $R Gamma(X, -)$ is applied, whenever $f: X -> Spec(k)$ is proper and $k$ is separably closed. 
]
#proof[
  Since $f$ is proper, $R f_* = R f_!$. By @existence-of-upper-shriek (4), there exists a natural isomorphism: 
  $
    RHHom_Lambda (R f_* cal(K), Lambda) cong R f^! RHHom_Lambda (cal(K), R f^! Lambda)
  $
  and in other words, $DD_(Spec(k)) R f_* cal(K) cong R f_* DD_X cal(K)$. We thus have an isomorphism: 
  $
    R f_* DD_X DD_X cal(K) cong DD_(Spec(k)) DD_(Spec(k)) R f_* cal(K) cong R f_* cal(K)
  $
  We claim that this isomorphism is induced by evaluation. That is, we need to check the commutativity of the following diagram: 
  // https://q.uiver.app/#r=typst&q=WzAsNSxbMCwwLCJSSEhvbV9MYW1iZGEgKFJISG9tX0xhbWJkYSAoUiBmXyogY2FsKEspLCBMYW1iZGEpLCBMYW1iZGEpIl0sWzAsMSwiUkhIb21fTGFtYmRhIChSIGZfKiBSSEhvbV9MYW1iZGEgKGNhbChLKSwgUiBmXiEgTGFtYmRhKSwgTGFtYmRhKSJdLFswLDIsIlIgZl8qIFJISG9tX0xhbWJkYSAoUkhIb21fTGFtYmRhIChjYWwoSyksIFIgZl4hIExhbWJkYSksIFIgZl4hIExhbWJkYSkiXSxbMiwwLCJSIGZfKiBjYWwoSykiXSxbMiwyLCJSIGZfKiBjYWwoSykiXSxbMyw0LCIiLDAseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkb3VibGUgYmFycmVkIn19fV0sWzAsMSwidGlsZGUiLDJdLFsyLDEsInRpbGRlIl0sWzMsMCwiZXYiLDJdLFs0LDIsImV2Il1d
  #align(center, diagram({
    node((0, 0), [$RHHom_Lambda (RHHom_Lambda (R f_* cal(K), Lambda), Lambda)$])
    node((0, 1), [$RHHom_Lambda (R f_* RHHom_Lambda (cal(K), R f^! Lambda), Lambda)$])
    node((0, 2), [$R f_* RHHom_Lambda (RHHom_Lambda (cal(K), R f^! Lambda), R f^! Lambda)$])
    node((2, 0), [$R f_* cal(K)$])
    node((2, 2), [$R f_* cal(K)$])
    edge((2, 0), (2, 2), "=")
    edge((0, 0), (0, 1), [$tilde$], label-side: right, "->")
    edge((0, 2), (0, 1), [$tilde$], label-side: left, "->")
    edge((2, 0), (0, 0), [$"ev"$], label-side: right, "->")
    edge((2, 2), (0, 2), [$"ev"$], label-side: left, "->")
  }))
  Upon uncurrying, the upper path becomes the map: 
  $
    R f_* cal(K) Lotimes_Lambda R f_* RHHom_Lambda (cal(K), R f^! Lambda) cong R f_* cal(K) Lotimes_Lambda RHHom_Lambda (R f_* cal(K), Lambda) ->^"ev" Lambda
  $
  while the lower path becomes: 
  $
    R f_* cal(K) Lotimes_Lambda R f_* RHHom_Lambda (cal(K), R f^! Lambda) -> R f_* (cal(K) Lotimes_Lambda RHHom_Lambda (cal(K), R f^! Lambda)) ->^"ev" R f_* R f^! Lambda ->^Tr Lambda
  $
  These two paths are formally equal. Thus we have shown that the evaluation $R f_* cal(K) -> R f_* DD_X DD_X cal(K)$ is an isomorphism. $k$ is a separably closed field, so this is equivalent to saying that $R Gamma(X, cal(K)) -> R Gamma(X, DD_X DD_X cal(K))$ is an isomorphism. 
]

/*
To proceed, we would have needed a limit formula to base change from an arbitrary field to a separably closed field. Instead, let's perform a devissage. 

#lemma(name: <base-field-extension-for-upper-shriek>)[
  Let $L\/k$ be any field extension, $f: X -> Y$ be a separated morphism between finite type $k$-schemes, and $f_L: X_L -> Y_L$ be its base change from $k$ to $L$. Then for any $cal(K) in D^b_#[ctf] (Y_et, Lambda)$, there is a canonical natural isomorphism: 
  $
    (R f^! cal(K))|_(X_L) cong R f_L^! (cal(K)|_(Y_L))
  $
]
#proof[
  Suppose for now that $f = i$ is a closed immersion, and take the complementary open immersion $j: U -> Y$. Then we have sections with support triangles: 
  $
    i_* R i^! cal(L) -> cal(L) -> R j_* j^(-1) cal(L) ->^(+1)
  $
  and: 
  $
    i_(L,*) R i_L^! cal(L)|_(Y_L) -> cal(L)|_(Y_L) -> R j_(L,*) j_L^(-1) cal(L)|_(Y_L) ->^(+1)
  $
  However, by generic base change, $(R j_* j^(-1) cal(L))|_(Y_L) cong R j_(L,*) j_L^(-1) cal(L)|_(Y_L)$. Hence on the first term of the distinguished triangle: 
  $
    i_(L,*) (R i^! cal(L))|_(X_L) cong (i_* R i^! cal(L))|_(Y_L) cong i_(L,*) R i_L^! cal(L)|_(Y_L)
  $
  and so $(R i^! cal(L))|_(X_L) cong R i_L^! cal(L)|_(Y_L)$. 

  Next, suppose that $f = p: AA^d_Y -> Y$. Then by relative Poincare duality, both sides are $cal(K)|_(X_L)(d)[2d]$ and are isomorphism. 

  Now for the general case, by picking an affine cover of $X$, there is an etale cover $j: U -> X$ s.t. $f compose j$ factors as $U ->^i AA^d_k ->^p Spec(k)$ for $i$ a closed immersion. Then by the previous too cases, the lemma holds for $f compose j$. Thus, 
  $
    j_L^(-1) (R f^! cal(K))|_(X_L) cong j_L^(-1) R f_L^! cal(K)|_(Y_L)
  $
  Since $j$ is surjective, by @surjective-pullback-conservative, this concludes that $R f^! cal(K))|_(X_L) cong R f_L^! cal(K)|_(Y_L)$. 
]

#lemma[
  Let $L\/k$ be any field extension and $X$ be a finite type $k$-scheme. Put $X_L = X otimes_k k_L$. Then for any $cal(K), cal(L) in D^b_#[ctf] (X_et, Lambda)$, 
  $
    RHHom_Lambda (cal(K), cal(L))|_(X_L) -> RHHom_Lambda (cal(K)|_(X_L), cal(L)|_(X_L))
  $
  is an isomorphism. 
]
#proof[
  By induction on $d = dim(X)$, we may assume that this lemma has been proved for all $X$ with $dim(X) <= d-1$. 

  By @resolution-of-ctf-complexes and truncations, it suffices to prove that for constructible flat sheaves $cal(F), cal(G)$ on $X$ of $Lambda$-modules: 
  $
    RHHom_Lambda (cal(F), cal(G))|_(X_L) cong RHHom_Lambda (cal(F)|_(X_L), cal(G)|_(X_L))
  $
  Since $cal(F)$ is constructible, there exists a dense open $U subset X$ on which $cal(F)$ is locally constant. By shrinking $U$ suitably, we may assume that $cal(F), cal(G)$ are both l.c.c. on $U$. Now pick complementary immersions $j: U -> X, i: Z -> X$ and $j_L: U_L -> X_L, i_L: Z_L -> X_L$. Then: 
  $
    RHHom_Lambda (i_* i^(-1) cal(F), cal(G))|_(X_L) &cong i_(L,*) (RHHom_Lambda (i^(-1) cal(F), R i^! cal(G))|_(Z_L)) \
    &cong i_(L,*) RHHom_Lambda (i_L^(-1) cal(F)|_(X_L), (R i^! cal(G))|_(Z_L)) #[by inductive hypothesis] \
    &cong i_(L,*) RHHom_Lambda (i_L^(-1) cal(F)|_(X_L), R i_L^! (cal(G)|_(X_L))) #[by previous lemma]\
    &cong RHHom_Lambda (i_(L,*) i_L^(-1) cal(F)|_(X_L), cal(G)|_(X_L))
  $
  Thus, by the extension by zero triangle, it suffices to prove that: 
  $
    RHHom_Lambda (j_! j^(-1) cal(F), cal(G))|_(X_L) cong RHHom_Lambda (j_(L,!) j_L^(-1) cal(F)|_(X_L), cal(G)|_(X_L))
  $
  Indeed, 
  $
    RHHom_Lambda (j_! j^(-1) cal(F), cal(G))|_(X_L) cong (R j_* RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G)))|_(X_L) cong R j_(L,*) (RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G))|_(U_L))
  $
  by generic base change, while: 
  $
    RHHom_Lambda (j_(L,!) j_L^(-1) cal(F)|_(X_L), cal(G)|_(X_L)) cong R j_(L,*) RHHom_Lambda (j_L^(-1) cal(F)|_(X_L), j_L^(-1) cal(G)|_(X_L))
  $
  Thus, it suffices to prove that: 
  $
    RHHom_Lambda (j^(-1) cal(F), j^(-1) cal(G))|_(U_L) cong RHHom_Lambda (j_L^(-1) cal(F)|_(X_L), j_L^(-1) cal(G)|_(X_L))
  $
  In other words, replacing $X$ with $U$, it suffices to prove that: 
  
  - For any l.c.c. flat sheaf of $Lambda$-modules $cal(F), cal(G)$ on $X$, #h(1fr)
    $
      RHHom_Lambda (cal(F), cal(G))|_(X_L) cong RHHom_Lambda (cal(F)|_(X_L), cal(G)|_(X_L))
    $

  There exists an etale cover $j: U -> X$ with $U$ affine s.t. $j^(-1) cal(F), j^(-1) cal(G)$ are both constant. It suffices to verify after pulling back along @surjective-pullback-conservative. Thus we may in fact assume that $cal(F), cal(G)$ are constant $ul(F), ul(G)$ for finite projective $Lambda$-modules $F,G$. Then we have seen that: 
  $
    RHHom_Lambda (cal(F), cal(G))|_(X_L) cong ul(Hom_Lambda (F, G)) cong RHHom_Lambda (cal(F)|_(X_L), cal(G)|_(X_L))
  $
  We are thereby done. 
]

#corollary(name: <dualizing-complex-and-base-field-ext>)[
  Let $k$ be any field and $X$ be a separated finite type $k$-scheme. Put $X_L = X otimes_k k_L$. Then there is a natural isomorphism: 
  $
    (DD_(X\/k) cal(K))|_(X_L) cong DD_(X_L\/k_L) cal(K)|_(X_L)
  $
  for all $cal(K) in D^b_#[ctf] (X_et, Lambda)$. 
]
#proof[
  Let $f: X -> Spec(k), f_L: X_L -> Spec(k_L)$ be the structure maps. By the previous lemma, 
  $
    (DD_(X\/k) cal(K))|_(X_L) &cong RHHom_Lambda (cal(K)|_(X_L), (R f^! ul(Lambda))|_(X_L)) \
    &cong RHHom_Lambda (cal(K)|_(X_L), R f_L^(!) ul(Lambda)) #[by @base-field-extension-for-upper-shriek] \
    &cong DD_(X_L\/k_L) cal(K)|_(X_L)
  $
  We are thereby done. 
]*/

To proceed, we need some more limit formulas. 

#lemma(name: <limit-formula-for-upper-shriek>)[
  (Limit formula for $R i^!$) Suppose that $X = invlim_(i >= 0) X_i$ is a noetherian scheme that is a projective limit of noetherian schemes under affine transition maps $u_(i,j): X_i -> X_j$. Denote by $u_i: X -> X_i$ the projections. Let $h_0: Z_0 -> X_0$ be a closed immersion, base changed to $h_i: Z_i -> X_i$ and $h: Z -> X$. Then for any system of sheaves $(cal(F)_i, phi_(i,j))$ on ${X_i}$ with limit sheaf $cal(F)$, the canonical map: 
  $
    dirlim_i (R^q h_i^! cal(F)_i)|_Z cong R^q h^! cal(F)
  $
]
#proof[
  Take complementary open immersions $g_i: U_i -> X_i$ and $g: U -> X$. Now $(g_i^(-1) cal(F)_i, g_i^(-1) phi_(i,j))$ is a system of sheaves on ${U_i}$ with limit sheaf $g^(-1) cal(F)$, so by the base change limit formula @limit-formula-for-base-change, we have: 
  $
    u_i^(-1) R^q g_(i,*) g_i^(-1) cal(F)_i cong R^q g_* g^(-1) cal(F)
  $
  Thus: 
  $
    dirlim_i (h_i^! cal(F)_i)|_Z &cong dirlim_i ker(h_i^(-1) cal(F)_i -> h_i^(-1) g_(i,*) g_i^(-1) cal(F)_i)|_Z \
    &cong ker(dirlim_i (h_i^(-1) cal(F)_i)|_Z -> dirlim_i (h_i^(-1) g_(i,*) g_i^(-1) cal(F)_i)|_Z) \
    &cong ker(h^(-1) cal(F) -> dirlim_i h^(-1) u_i^(-1) g_(i,*) g_i^(-1) cal(F)_i) \
    &cong ker(h^(-1) cal(F) -> h^(-1) g_* g^(-1) cal(F)) cong h^! cal(F)
  $
  Similarly, replacing all $ker$ with $coker$ in the deduction above yields: 
  $
    dirlim_i (R^1 h_i^! cal(F)_i)|_Z cong R^1 h^! cal(F)
  $
  Finally, for $q >= 2$, 
  $
    dirlim_i (R^q h_i^! cal(F)_i)|_Z &cong dirlim_i (h_i^(-1) R^(q-1) g_(i,*) g_i^(-1) cal(F)_i)|_Z \
    &cong dirlim_i h^(-1) u_i^(-1) R^(q-1) g_(i,*) g_i^(-1) cal(F)_i \
    &cong h^(-1) R^(q-1) g_* cal(F) cong R^q h^! cal(F)
  $
]

#lemma(name: <limit-formula-for-hom-and-ext>)[
  Suppose that $X = invlim_(i >= 0) X_i$ is a noetherian scheme that is a projective limit of noetherian schemes under affine transition maps $u_(i,j): X_i -> X_j$. Denote by $u_i: X -> X_i$ the projections.  
  
  Suppose that $cal(K)_0 in D^b_c ((X_0)_et, Lambda)$ with $cal(K)_i = cal(K)_0|_(X_i)$ and $cal(K) = cal(K)_0|_X$, and $(cal(G)_i, phi_(i,j))$ is a system of sheaves on ${X_i}$ with limit sheaf $cal(G)$. Then the canonical maps: 
  $
    dirlim_i h^q (RHom_Lambda (cal(K)_i, cal(G)_i)) -> h^q (RHom_Lambda (cal(K), cal(G))) \

    dirlim_i u_i^(-1) h^q (RHHom_Lambda (cal(K)_i, cal(G)_i)) -> h^q (RHHom_Lambda (cal(K), cal(G)))
  $
  are isomorphisms. 

  In particular, by truncations and way-out arguments, for all $cal(L)_0 in D^+ ((X_0)_et, Lambda)$ with $cal(L)_i = cal(L)_0|_(X_i)$ and $cal(L) = cal(L)_0|_X$, the canonical maps: 
  $
    dirlim_i h^q (RHom_Lambda (cal(K)_i, cal(L)_i)) -> h^q (RHom_Lambda (cal(K), cal(L))) \

    dirlim_i u_i^(-1) h^q (RHHom_Lambda (cal(K)_i, cal(L)_i)) -> h^q (RHHom_Lambda (cal(K), cal(L)))
  $
]
#proof[
  We check the $RHom$ statement first. Both sides are cohomological in both $cal(K)_0$ and $(cal(G)_i, phi_(i,j))$. By the way-out lemma, it thus suffices to check when $cal(K)_0 = cal(F)_0$ is a constructible sheaf. Now pick a resolution: 
  $
    dots.c -> cal(H)^((p))_0 -> dots.c -> cal(H)^((1))_0 -> cal(H)^((0))_0 -> cal(F)_0 -> 0
  $
  in which $cal(H)^((p))_0 = j^((p))_(0,!) ul(Lambda)$ for $j^((p))_0: U^((p))_0 -> X_0$ etale from an affine scheme. Then we have a first quadrant spectral sequence from hypercohomology: 
  $
    E_(1,i)^(p,q) = Ext^q_Lambda (cal(H)_i^((p)), cal(G)_i) => Ext^(p+q)_Lambda (cal(F)_i, cal(G)_i)
  $
  and hence in the limit, 
  $
    E_1^(p,q) = dirlim_i Ext^q_Lambda (cal(H)_i^((p)), cal(G)_i) => dirlim_i Ext^(p+q)_Lambda (cal(F)_i, cal(G)_i)
  $
  On the other hand, there is another spectral sequence: 
  $
    tilde(E)_1^(p,q) = Ext^q_Lambda (cal(H)^((p)), cal(G)) => Ext^(p+q)_Lambda (cal(F), cal(G))
  $
  By comparison of the spectral sequences $E_1^(p,q)$ and $tilde(E)_1^(p,q)$, we see that it suffices to prove this lemma whenever $cal(F)_0 = j_(0,!) ul(Lambda)$ for an etale $j: U_0 -> X_0$ from an affine. Similarly, replacing all $Ext$ with $EExt$ should give the $RHHom$ statement. Now in this case: 
  $
    dirlim_i Ext^q_Lambda (j_(i,!) ul(Lambda), cal(G)_i) cong dirlim_i H^q (U_i, cal(G)_i) cong H^q (U, cal(G)) #[by @limit-formula-composite]
  $
  and: 
  $
    dirlim_i EExt^q_Lambda (j_(i,!) ul(Lambda), cal(G)_i) cong dirlim_i R^q j_(i,*) j_i^(-1) cal(G)_i cong R^q j_* j^(-1) cal(G) cong EExt^q_Lambda (j_! ul(Lambda), cal(G)) #[by @relative-limit-formula-composite] 
  $
  We are thereby done. 
  // $
  //   cal(S)_0 = {Z_0 subset X_0 #[closed] :& dirlim_i h^q (RHom_Lambda (cal(F)_i, cal(G)_i)) cong h^q (RHom_Lambda (cal(F), cal(G))) \
  //   & #[for all constructible $cal(F)_0$ s.t. $supp(cal(F)_0) subset Z_0$] \
  //   & #[for all system of sheaves $(cal(G)_i, phi_(i,j))$ on ${X_i}$ with limit $cal(G)$]}
  // $
  // If an object has subscript $0$, we change this subscript to $i$ or drop it to denote the obvious meaning of pulling back to $X_i$ or $X$, unless otherwise stated. 

  // Suppose that $Z_0 subset X_0$ has the property that every proper closed subset $W_0 subset.neq Z_0$ is in $cal(S)_0$. Take a immersion $Z_0 ->^(h_0) X_0$. Then for any constructible $cal(F)_0$ with $supp(cal(F)_0) subset Z_0$, we may write $cal(F)_0 = h_(0,*) h_0^(-1) cal(F)_0$. Pick a Zariski open $j_0: U_0 -> Z_0$ s.t. $j_0^(-1) h_0^(-1) cal(F)_0$ is l.c.c, and take a complementary closed immersion $w_0: W_0 -> Z_0$. We now have the exact sequences: 
  // $
  //   0 -> h_(0,*) j_(0,!) j_0^(-1) h_0^(-1) cal(F)_0 -> cal(F)_0 -> w_(0,*) w_0^(-1) cal(F)_0 -> 0
  // $
  // Now $supp(w_(0,*) w_0^(-1) cal(F)_0) subset W_0 in cal(S)_0$ has been dealt with, so it suffices to deal with the first term $j_(0,!) j_0^(-1) h_0^(-1) cal(F)_0$. Now: 
  // $
  //   RHom_Lambda (h_(i,*) j_(i,!) j_i^(-1) h_i^(-1) cal(F)_i, cal(G)_i) cong RHom_Lambda (j_i^(-1) h_i^(-1) cal(F)_i, j_i^(-1) R h_i^! cal(G)_i)
  // $
  // By truncations and standard way-out arguments, to prove that: 
  // $
  //   dirlim_i RHom_Lambda (j_i^(-1) h_i^(-1) cal(F)_i, j_i^(-1) R h_i^! cal(G)_i) cong dirlim_i RHom_Lambda (j^(-1) h^(-1) cal(F), j^(-1) R h^! cal(G))
  // $
  // it suffices to prove: 
  // $
  //   dirlim_i RHom_Lambda (j_i^(-1) h_i^(-1) cal(F)_i, j_i^(-1) R^q h_i^! cal(G)_i) cong dirlim_i RHom_Lambda (j^(-1) h^(-1) cal(F), j^(-1) R^q h^! cal(G))
  // $
  // for each $q$. Now by @limit-formula-for-upper-shriek, $(R^q h_i^! cal(G)_i)$ is a system of sheaves on ${Z_i}$ with limit $R^q h_i^! cal(G)$, and hence, $(j_i^(-1) R^q h_i^(-1) cal(G)_i)$ is a system of sheaves on $U_i$ with limit $j^(-1) R^q h^! cal(G)$. 
  
  // - $j_0^(-1) h_0^(-1) cal(F)_0$ is a l.c.c. sheaf, and by @limit-formula-for-upper-shriek
]

#theorem[
  Suppose that $f: X -> Spec(k)$ is separated of finite type. Then the biduality map: 
  $
    cal(K) -> DD_X DD_X cal(K)
  $
  is an isomorphism for all $cal(K) in D^b_#[ctf] (X_et, Lambda)$. 
]
#proof[
  We perform induction on $d = dim(X)$. Thus, we assume that the biduality map is an isomorphism for all fields $k$ and all separated finite type $k$-schemes $X$ with $dim(X) <= d-1$. 

  We may check after pulling back to $X otimes_k k^sep$. For every finite separable extension $L\/k$, 
  $
    (DD_(X\/k) cal(K))|_(X_L) cong DD_(X_L\/L) (cal(K)|_(X_L))
  $
  naturally with base change. Thus by @limit-formula-for-hom-and-ext, taking a limit over all $L$, 
  $
    (DD_(X\/k) cal(K))|_(X_(k^sep)) cong DD_(X_(k^sep)\/k^sep) (cal(K)|_(X_(k^sep)))
  $
  Thus after replacing $k, X$ with $k^sep, X otimes_k k^sep$, we may assume that $k$ is separably closed. By topological invariance we may further replace $k$ with $ol(k)$ to assume that it is algebraically closed. 

    Pick a compactification $X ->^j ol(X) ->^(ol(f)) Spec(k)$. Replacing $ol(X)$ by the schematic closure of $X$, we may assume that $X$ is dense in $ol(X)$, and hence $dim(ol(X)) = dim(X)$.

  For every $cal(L) in D^b_#[ctf] (ol(X)_et, Lambda)$, @existence-of-upper-shriek (0)(1)(3) gives a natural isomorphism:
  $
    DD_X (j^(-1) cal(L))
    &cong RHHom_Lambda (j^(-1) cal(L), R j^! R ol(f)^! ul(Lambda)) cong RHHom_Lambda (j^(-1) cal(L), j^(-1) R ol(f)^! ul(Lambda)) \
    &cong j^(-1) RHHom_Lambda (cal(L), R ol(f)^! ul(Lambda)) = j^(-1) DD_(ol(X)) cal(L)
  $

  Taking first $cal(L) = j_! cal(K)$ and then
  $cal(L) = DD_(ol(X)) j_! cal(K)$ gives:
  $
    DD_X cal(K)
    &cong j^(-1) DD_(ol(X)) j_! cal(K), \

    DD_X j^(-1) DD_(ol(X)) j_! cal(K)
    &cong j^(-1) DD_(ol(X)) DD_(ol(X)) j_! cal(K)
  $
  and thus identifies $DD_X DD_X cal(K) cong j^(-1) DD_(ol(X)) DD_(ol(X)) j_! cal(K)$. These identifications are compatible with biduality: the map
  $
    cal(K) -> DD_X DD_X cal(K)
  $
  is identified with the restriction by $j^(-1)$ of
  $
    j_! cal(K) -> DD_(ol(X)) DD_(ol(X)) j_! cal(K).
  $
  Indeed, this follows by restricting the evaluation pairing defining the latter map. Since $j_! cal(K) in D^b_#[ctf] (ol(X)_et, Lambda)$ by @finiteness-of-six-functors, biduality on the proper scheme $ol(X)$ implies biduality on $X$.

  Hence, to prove biduality for $DD_X$, it suffices to prove biduality for $DD_(ol(X))$. We may therefore assume that $X$ is proper over $k$. Fix $cal(K) in D^b_#[ctf] (X_et, Lambda)$ and form the cone:
  $
    cal(K) -> DD_X DD_X cal(K) -> Delta ->^(+1)
  $
  By @partial-biduality-in-proper-case, we see that $R Gamma(X, Delta) = 0$. We claim that $Delta$ is supported on finitely many closed points of $X$. 

  #proof_[Proof of claim][
    For an affine open $U subset X$, pulling the distinguished triangle above to $U$ yields the triangle: 
    $
      cal(K)|_U -> DD_U DD_U cal(K)|_U -> Delta|_U ->^(+1)
    $
    Thus, replacing $X$ with $U$, we may assume that $X$ is affine (and forget above the assumption that $X$ is proper over $k$, since that is not useful). Pick a closed immersion $i: X -> AA^m_k$ and take projections $pi_1, dots.c, pi_m: AA^m_k -> AA^1_k$. Let $eta = Spec(k(t))$ be the generic point of $AA^1_k$, and $X_(eta,j) = h^(-1) (pi_j^(-1) (eta))$. Then: 
    $
      dim(X_(eta,j)) <= dim(X) - 1 < d
    $
    Thus, the inductive hypothesis may be applied, and $cal(K)|_(X_(eta,j)) -> DD_(X_(eta,j)\/k(t)) DD_(X_(eta,j)\/k(t)) cal(K)|_(X_(eta,j))$ is an isomorphism. 

    We claim that: 
    $
      (DD_X DD_X cal(K))|_(X_(eta,j)) cong DD_(X_(eta,j)\/k(t)) DD_(X_(eta,j)\/k(t)) cal(K)|_(X_(eta,j))
    $
    compatibly with evaluation. Indeed, consider the diagram with Cartesian squares: 
    // https://q.uiver.app/#r=typst&q=WzAsNyxbMCwxLCJYIl0sWzEsMSwiQUFebV9rIl0sWzIsMSwiQUFeMV9rIl0sWzMsMSwiU3BlYyhrKSJdLFsyLDAsImV0YSJdLFsxLDAsIkFBXihtLTEpX2V0YSJdLFswLDAsIlhfKGV0YSxqKSJdLFs2LDUsImknX2oiXSxbNSw0LCJwaSciXSxbMCwxLCJpIiwyXSxbMSwyLCJwaV9qIiwyXSxbMiwzXSxbNCwyLCJqIl0sWzUsMSwiaiciXSxbNiwwLCJqJyciLDJdXQ==
    #align(center, diagram({
      node((0, 1), [$X$])
      node((1, 1), [$AA^m_k$])
      node((2, 1), [$AA^1_k$])
      node((3, 1), [$Spec(k)$])
      node((2, 0), [$eta$])
      node((1, 0), [$AA^(m-1)_eta$])
      node((0, 0), [$X_(eta,j)$])
      edge((0, 0), (1, 0), [$i'_j$], label-side: left, "->")
      edge((1, 0), (2, 0), [$pi'$], label-side: left, "->")
      edge((0, 1), (1, 1), [$i$], label-side: right, "->")
      edge((1, 1), (2, 1), [$pi_j$], label-side: right, "->")
      edge((2, 1), (3, 1), "->")
      edge((2, 0), (2, 1), [$j$], label-side: left, "->")
      edge((1, 0), (1, 1), [$j'$], label-side: left, "->")
      edge((0, 0), (0, 1), [$j''$], label-side: right, "->")
    }))
    Put $g_j: X ->^i AA^m_k ->^(pi_j) AA^1_k$. Then: 
    $
      DD_X cal(K) = RHHom_Lambda (cal(K), R g_j^! ul(Lambda)(1)[2])
    $
    Thus by @limit-formula-for-hom-and-ext and @limit-formula-for-upper-shriek, 
    $
      (DD_X cal(K))|_(X_(eta,j)) cong RHHom_Lambda (cal(K)|_(X_(eta,j)), R g'_j^! ul(Lambda))(1)[2]
    $
    Dualizing twice yields a canonical isomorphism $(DD_X DD_X cal(K))|_(X_(eta,j)) cong DD_(X_(eta,j)\/k(t)) DD_(X_(eta,j)\/k(t)) cal(K)|_(X_(eta,j))$, further isomorphic to $cal(K)|_(X_(eta,j))$ by the inductive hypothesis. Thus, in particular $Delta|_(X_(eta,j)) = 0$. //However, by @limit-formula-for-hom-and-ext, 
    // $
    //   h^q (DD_X DD_X cal(K))|_(X_(eta,j)) cong dirlim_(U subset AA^1_k) h^q (DD_X DD_X cal(K))|_(g_j^(-1) (U))
    // $
    // as a limit over opens of $AA^1_k$. Thus, passing through the distinguished triangle, 
    // $
    //   h^q (Delta)|_(X_(eta,j)) cong dirlim_(U subset AA^1_k) h^q (Delta)|_(g_j^(-1) (U))
    // $
    Now by @limit-formula-for-hom-and-ext, since $Delta in D^b_c$, 
    $
      0 = Hom_Lambda (Delta|_(X_(eta,j)), Delta|_(X_(eta,j))) = dirlim_(U subset AA^1_k) Hom_Lambda (Delta|_(g_j^(-1)(U)), Delta|_(g_j^(-1)(U)))
    $
    where the limit ranges over all nonempty opens of $AA^1_k$. Thus $id$ on RHS must pass to $0$ at some further stage. But $id$ must also pass to $id$, so $id = 0$ at some finite stage in the limit on RHS. Thus, for some dense open $U_j subset AA^1_k$, $Delta|_(g_j^(-1)(U_j)) = 0$. 

    Pick $U_1, dots.c, U_m subset AA^1_k$ this way for all $j = 1,dots.c,m$. Then: 
    $
      Delta|_(union.big_(j=1)^m g_j^(-1)(U_j)) = 0
    $
    Now: 
    $
      X - union.big_(j=1)^m g_j^(-1)(U_j) &= i^(-1) (AA^m_k - union.big_(j=1)^m pi_j^(-1) (U_j)) \
      &= i^(-1) ((AA^1_k - U_1) times_k dots.c times_k (AA^1_k - U_m))
    $
    However each $AA^1_k - U_j$ is only finitely many closed points $Spec(k)$. Thus $X - union.big_(j=1)^m g_j^(-1)(U_j)$ is only finitely many closed points $Spec(k)$, and so $Delta$ is supported on finitely many closed points. 
  ]
  Now $Delta$ is supported on finitely many closed points $x_1, dots.c, x_m in X$, all isomorphic to $Spec(k)$. Thus: 
  $
    Delta = oplus.big_(j=1)^m x_(j,*) M_j
  $
  for some complexes $M_j in D((x_j)_et, Lambda) cong D(Lambda)$. However, we have seen that $0 = R Gamma(X, Delta)$, so: 
  $
    0 = R Gamma(X, Delta) = oplus.big_(j=1)^m M_j
  $
  Thus it must be that each $M_j = 0$, and so $Delta = 0$. This concludes the proof that $cal(K) -> DD_X DD_X cal(K)$ is an isomorphism. 
]

To summarize the discussion: 

#theorem(name: <verdier-duality>)[
  (Verdier duality) For any field $k$ and any $n$-torsion noetherian ring $Lambda$ s.t. $n in k^times$, for every separated $X$ of finite type over $k$, 
  $
    DD_X = DD_(X\/k): D^b_#[ctf] (X_et, Lambda)^opp &-> D^b_#[ctf] (X_et, Lambda) \
    
    cal(K) &|-> RHHom_Lambda (cal(K), R f^! Lambda)
  $
  is identified as a contravariant involution under the biduality map $cal(K) ->^tilde DD_X DD_X cal(K)$. For any morphism $f: X -> Y$ between separated $k$-schemes of finite type, we have natural identifications: 
  $
    DD_Y compose R f_* cong R f_! compose DD_X \
    DD_Y compose R f_! cong R f_* compose DD_X \
    DD_X compose f^(-1) cong R f^! compose DD_Y \
    DD_X compose R f^! cong f^(-1) compose DD_Y
  $
  on $D^b_#[ctf]$. 
]
#proof[
  The involution part is proved in the previous theorem. For the four identities, 
  $
    DD_Y compose R f_! cong R f_* compose DD_X
  $
  is formal and is just @existence-of-upper-shriek (4). The statement $DD_Y compose R f_* cong R f_! compose DD_X$ thus follows from biduality. Now the remaining two statements on $f^(-1), R f^!$ follow from adjunction on the two statements already proved on $R f_*, R f_!$. 
]
