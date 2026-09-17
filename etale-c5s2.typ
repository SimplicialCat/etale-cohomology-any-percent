#import "void-import.typ": *
== Etale cohomology of quasi-coherent sheaves

#lemma[
  Let $U = Spec(A)$ be an affine scheme, and $cal(M) = tilde(M) in QCoh(U)$ be a quasi-coherent sheaf. Then: 
  $
    H^q (U, cal(M)_et) = 0, forall q >= 1
  $
]
#proof[
  We first prove for Cech cohomology, i.e: 
  $
    caron(H)^q (U, cal(M)_et) = 0, forall q >= 1
  $
  For this, we prove vanishing for a cofinal system of etale covers of $U$. Since $U$ is affine and so quasi-compact, every etale cover of $U$ is refined by one consisting of finitely many affine schemes. The Cech cohomology of such a cover is equal to the Cech cohomology of the cover consisting of a single map, obtained by taking the disjoint union. As such, it suffices to show that for etale covers of the shape $cal(U) = {U' = Spec(A') -> U}$, 
  $
    caron(H)^q (cal(U), cal(M)_et) = 0, forall q >= 1
  $
  Now since $U' ->> U$ is surjective etale, $A -> A'$ is faithfully flat. The Cech complex of $cal(U)$ is thus: 
  $
    0 -> M otimes_A A' -> dots.c -> M otimes_A A^((q)) -> M otimes_A A^((q+1)) -> dots.c
  $
  This is just the Amitsur complex with the term $M$ removed, and so is exact at all $q >= 1$ by @amitsur-complex-exact. We are thereby done with the proof for Cech cohomology. 

  We now pass to etale cohomology with the Cech-to-derived-functor spectral sequence and induction. Since $caron(H)^1 (U, -) = H^1 (U, -)$, we are already done with $q = 1$. Suppose that the lemma holds for all $0 < q < n$ and all quasi-coherent sheaves on affine schemes. Consider the Cech-to-derived-functor spectral sequence: 
  $
    E_2^(p,q) = caron(H)^p (U, ul(H)^q (cal(M)_et)) => H^(p+q) (U, cal(M)_et)
  $
  We claim that this spectral sequence vanishes for all $0 < q < n$. Since $U$ is affine, it is quasi-compact, so we may prove that: 
  $
    caron(H)^p (cal(U), ul(H)^q (cal(M)_et)) = 0
  $
  for all $0 < q < n$ and all $cal(U) = {U_i = Spec(B_i) -> U}_(1<=i<=m)$ consisting of finitely many affine schemes. Then by @pullback-along-etale-morphism-derived, the $p$-th term of the Cech complex of $ul(H)^q (cal(M)_et)$ is the direct product of terms of the shape: 
  $
    H^q (U_(i_0,dots.c,i_p), cal(M)_et) = H^q (U_(i_0,dots.c,i_p), u_(i_0,dots.c,i_p)^(-1) cal(M)_et)
  $
  where $u_(i_0,dots.c,i_p): U_(i_0,dots.c,i_p) := U_(i_0) times_U dots.c times_U U_(i_p) -> U$ is affine etale, and $u_(i_0,dots.c,i_p)^(-1) cal(M)_et = (u_(i_0,dots.c,i_p)^* cal(M))_et$, as can be checked section-wise. 

  However, whenever $0 < q < n$, all terms of this shape are $0$ by the inductive hypothesis. In other words, $caron(H)^p (U, ul(H)^q (cal(M)_et)) = 0$ for all $0 < q < n$, giving a horizontal vanishing strip for the Cech-to-derived-functor spectral sequence. Applying the modified five term exact sequence, we obtain an exact sequence: 
  $
    0 -> caron(H)^n (U, cal(M)_et) -> H^n (U, cal(M)_et) -> caron(H)^0 (U, ul(H)^n (cal(M)_et)) -> dots.c
  $
  Now $caron(H)^n (U, cal(M)_et) = 0$ as proved previously, and $caron(H)^0 (U, ul(H)_n (cal(M)_et)) = 0$ by @cech-h0-of-hq-psh-vanish. We are thereby done showing $H^n (U, cal(M)_et) = 0$.  
]

#theorem(name: <etale-cohom-of-qcoh-sheaf>)[
  Let $X$ be any scheme and $cal(M) in QCoh(X)$. Then there are natural isomorphisms: 
  $
    H^q_et (X, cal(M)_et) cong H^q_#[Zar] (X, cal(M)), forall q >= 0
  $
  between the etale cohomology of $cal(M)_et$ and the Zariski cohomology of $cal(M)$. 
]
#proof[
  Consider the forgetful functor: 
  $
    epsilon: cAb(X_et) -> cAb(X_#[Zar])
  $
  from etale sheaves on $X$ to Zariski sheaves on $X$. Since left exactness for both etale and Zariski sheaves are measured section-wise, $epsilon$ is a left exact functor. We want to apply the Grothendieck-Leray spectral sequence to the composition: 
  // https://q.uiver.app/#r=typst&q=WzAsMyxbMCwxLCJjQWIoWF9ldCkiXSxbMiwxLCJjQWIiXSxbMSwwLCJjQWIoWF8jW1phcl0pIl0sWzIsMSwiR2FtbWEoWCwtKSJdLFswLDEsIkdhbW1hKFgsLSkiLDJdLFswLDIsImVwc2lsb24iXV0=
  #align(center, diagram({
    node((-1, 0), [$cAb(X_et)$])
    node((1, 0), [$cAb$])
    node((0, -1), [$cAb(X_#[Zar])$])
    edge((0, -1), (1, 0), [$Gamma(X, -)$], label-side: left, "->")
    edge((-1, 0), (1, 0), [$Gamma(X, -)$], label-side: right, "->")
    edge((-1, 0), (0, -1), [$epsilon$], label-side: left, "->")
  }))
  For this, we need to show that $epsilon$ sends injectives to ${H^q_#[Zar] (X, -)}_(q>=0)$-acyclics. 

  #lemma[
    Given additive functors $F: cal(A) -> cal(B), G: cal(B) -> cal(C)$ between abelian categories, where $cal(A), cal(B)$ has enough injectives. Suppose that there exists a collection $cal(I)$ of injectives of $cal(A)$ s.t:
    
    - Every object of $cal(A)$ embeds into an object in the collection $cal(I)$; 

    - $F$ sends every object of $cal(I)$ to $G$-acyclics. 

    Then $F$ sends injectives to $G$-acyclics. 
  ]
  #proof[
    For any injective $I in cal(A)$, embed it as $I ->^i I_0$ where $I_0 in cal(I)$, and form the cokernel: 
    $
      0 -> I ->^i I_0 -> coker(i) -> 0
    $
    Then by injectivity of $I$, this exact sequence splits, identifying $I_0 = I oplus coker(i)$. Thus, $F(I_0) = F(I) oplus F(coker(i))$, and for each $q >= 1$, 
    $
      0 = R^q G (F(I_0)) = R^q G (F(I)) oplus R^q G (F(coker(i)))
    $
    and so $R^q G(F(I)) = 0, forall q >= 1$. Hence $F(I)$ is a $G$-acyclic object. 
  ]
  By the Godement resolution, every sheaf in $cAb(X_et)$ embeds into an injective sheaf of the shape: 
  $
    product_(x in X) ol(x)_* I_x
  $
  After applying the forgetful functor, this sheaf goes to the Zariski sheaf $product_(x in X) x_* I_x$, a direct product of skyscraper sheaves. Such a sheaf is flasque, hence ${H^q_#[Zar] (X, -)}_(q>=0)$-acyclic. 
  #remark[
    If we resort to general topos theory, we see that there is a pair of maps between sites $X_et arrows.rl X_#[Zar]$, inducing an exact left adjoint to $epsilon$, making it send injectives to injectives. However, I prefer to use a simple readable ad hoc argument, instead of introducing general topoi just to get a technical condition. 
  ]
  
  By the Grothendieck-Leray spectral sequence, we get a spectral sequence: 
  $
    E_2^(p,q) = H^p_#[Zar] (X, R^q epsilon (cal(M)_et)) => H^(p+q)_et (X, cal(M)_et)
  $
  Therefore, to show that $H^p_#[Zar] (X, cal(M)) cong H^p_et (X, cal(M)_et)$, it suffices to show that this spectral sequence degenerates, by showing that $R^q epsilon (cal(M)_et) = 0$ for all $q >= 1$. 

  For any object $cal(F) in cAb(X_et)$, take an injective resolution $0 -> cal(F) -> cal(I)^bullet$. We then apply $epsilon$ to this chain complex to get $0 -> epsilon(cal(F)) -> epsilon(cal(I)^bullet)$. Now: 
  $
    R^q epsilon (cal(F)) = h^q (0 -> epsilon(cal(I)^bullet))
  $
  By the theory of Zariski sheaves, this sheaf is the Zariski sheafification of $U |-> h^q (0 -> epsilon(cal(I)^bullet)(U)) = H^q_et (U, cal(F))$. As such, to show that $R^q epsilon (cal(M)_et) = 0$, it suffices to show that $H^q_et (U, cal(M)_et) = 0$ for elements $U$ of a basis of the Zariski topology of $X$. However, 
  $
    H^q_et (U, cal(M)_et) = H^q_et (U, (cal(M)|_U)_et) = 0
  $
  for all affine opens $U subset X$, by the previous lemma. We are thereby done. 
]
