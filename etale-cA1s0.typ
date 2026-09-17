#import "void-import.typ": *

The passage to limit is a technique used to reduce statements on general qcqs schemes, to statements on noetherian schemes. When phrased in full generality, it may be used for other purposes, such as for spreading out properties on local rings to open neighborhoods. 

The intuition of this technique goes as follows: Given an affine scheme $X = Spec(A)$, every element of $A$ is contained in a subring of $A$ that is finite type over $ZZ$. In other words, let ${A_lambda}_lambda$ be the directed set of all subrings of $A$ finite type over $ZZ$, then: 
$
  A = dirlim_lambda A_lambda
$
and so: 
$
  X = Spec(A) = invlim_lambda Spec(A_lambda)
$
is a projective limit of noetherian schemes, or more specifically, of schemes of finite type over $ZZ$. Furthermore, given a morphism $A -> B$ of finite presentation, we may write: 
$
  B cong A[t_1, dots.c, t_n]/((g_1 (arrow(t)), dots.c, g_m (arrow(t))))
$
defined by finitely many generators and relations. However, each polynomial $g_i in A[t_1, dots.c, t_n]$ can only have finitely many coefficients, each of them contained in some finite stage $A_lambda$. As such, there exists some finite stage $lambda_i$ s.t. $g_i in A_(lambda_i) [t_1, dots.c, t_n]$. Taking an upper bound $mu$ of $lambda_1, dots.c, lambda_m$, we see that there exists a finite stage $mu$ s.t. $g_1, dots.c, g_m in A_mu [t_1, dots.c, t_n]$. Now take for all $lambda >= mu$: 
$
  B_lambda = (A_lambda [t_1, dots.c, t_n])/((g_1 (arrow(t)), dots.c, g_m (arrow(t))))
$
and we immediately see that for all $lambda >= mu$, $A_lambda -> B_lambda$ is the base change of $A_mu -> B_mu$ along $A_mu -> A_lambda$. Furthermore, $A -> B$ is the base change of $A_lambda -> B_lambda$ along $A_lambda -> A$. 

In other words, any morphism $A -> B$ of finite presentation must come from a morphism $A_mu -> B_mu$ at some finite stage, also of finite presentation. 

We next consider properties of the morphism $A -> B$. For demonstration purposes, we take one simple property as our example: That $A -> B$ is surjective, i.e. $Spec(B) -> Spec(A)$ is a closed immersion. In other words, each $t_i in B$ is contained in the image of $A -> B$, or there exists $h_(i,j) in A[t_1, dots.c, t_n]$ s.t. 
$
  t_i = sum_(j=1)^m h_(i,j) g_j, forall 1 <= i <= n
$
However, the finite set of polynomials ${h_(i,j)}$ only has finitely many coefficients, which may be all contained in some finite stage $A_(mu')$. As such, enlarging $mu$ if necessary, we see that for all $lambda >= mu$, $A_lambda -> B_lambda$ is surjective. 

These paragraphs above are not for rigorously proving any theorems. However, they establish the following intuition: 

- A scheme satisfying a certain finiteness condition (say, affine) is the projective limit of noetherian schemes; 

- A morphism to such a scheme that satisfies a certain finiteness condition (say, affine and finitely presented) must come from base changing a morphism at a finite stage in the limit; 

- Certain properties (say, being a closed immersion) on morphisms descend to sufficiently late stages in the limit. 

The rest of this appendix states various theorems resolving what "certain" in the three statements above precisely means in the most general way. We will not provide any proofs, as they seem too technical, even for these rather verbose lecture notes. Instead, we provide references to the Stacks Project. 

The first problem to answer is approximation of schemes. It turns out that the correct finiteness condition is being qcqs: 
#theorem(name: <absolute-noetherian-approx>)[
  (Absolute noetherian approximation) Any qcqs scheme $X$ can be written as a projective limit: 
  $
    X = invlim_i X_i
  $
  in the category of schemes, which all transition maps are affine, and every $X_i$ is of finite type over $ZZ$. 
]
#proof[
  See #cite-stacks("01ZA")[Lemma 32.5.4]. 
]

#theorem(name: <relative-approx>)[
  (Relative approximation) Given any morphism $f: X -> S$ of schemes in which $X$ is qcqs and $S$ is quasi-separated, $X$ can be written as a projective limit: 
  $
    X = invlim_i X_i
  $
  in the category of schemes, in which every $X_i$ is an $S$-scheme of finite presentation over $S$, and all transition maps are affine $S$-morphisms. 
]
#proof[
  See #cite-stacks("09MV")[Lemma 32.7.2]. 
]

The second question is approximation of morphisms, where the correct finiteness condition is finite presentation: 

#theorem(name: <passage-to-limit-of-morphisms>)[
  Let $S = invlim_i S_i$ be a projective limit of qcqs schemes with affine transition maps. Then: 

  + Given any morphism $X -> S$ of finite presentation, there exists some finite stage $i$ and some morphism $X_i -> S_i$ of finite presentation, whose base change along $S -> S_i$ is exactly $X -> S$. 

  + Given a morphism $phi: X -> Y$ of $S$-schemes so that $X = X_i times_(S_i) S, Y = Y_i times_(S_i) S$ for some finite stage $i$ and finitely presented $S_i$-schemes $X_i, Y_i$, there exists some further stage $i' >= i$ s.t. there exists a morphism $phi_(i'): X_(i') -> Y_(i')$ whose base change along $S -> S_(i')$ is $phi$. 

  + Given a finite stage $i$ and finitely presented $S_i$-schemes $X_i, Y_i$ with two morphisms $phi_i, psi_i: X_i -> Y_i$ whose base changes along $S -> S_i$ are equal, there exists a further stage $i' >= i$ s.t. the base changes of $phi_i$ and $psi_i$ along $S_(i') -> S_i$ are equal. 
]
#proof[
  See #cite-stacks("01ZM")[Lemma 32.10.1]. 
]

In plain words, 

- Finitely presented $S$-schemes come from base changing finitely presented $S_i$-schemes for some $i$; 

- Morphisms between finitely presented $S$-schemes come from base changing morphisms between $S_i$-schemes for some $i$; 

- Morphisms that are equal in the limit become equal at a finite stage. 

A limit result also exists for quasi-coherent sheaves with finite presentation. 

#theorem(name: <passage-to-limit-of-sheaves>)[
  Let $S = invlim_i S_i$ be a projective limit of qcqs schemes with affine transition maps. Denote the transition morphisms by $f_(i',i): S_(i') -> S_i$ and projections $f_i: S -> S_i$. Then:
  
  + Given any $cal(O)_S$-module $cal(F)$ of finite presentation, there exists a finite stage $i$ and an $cal(O)_(S_i)$-module $cal(F)_i$ of finite presentation s.t. $cal(F) cong f_i^* cal(F)_i$. 
  
  + Given $cal(O)_(S_i)$-modules $cal(F)_i, cal(G)_i$ of finite presentation and a morphism $phi: f_i^* cal(F)_i -> f_i^* cal(G)_i$, there exists a further stage $i' >= i$ and a morphism $phi_(i'): f_(i',i)^* cal(F)_i -> f_(i',i)^* cal(G)_i$ s.t. $phi = f_(i')^* phi_(i')$. 
  
  + Given $cal(O)_(S_i)$-modules $cal(F)_i, cal(G)_i$ of finite presentation and morphisms $phi_i, psi_i: cal(F)_i -> cal(G)_i$ s.t. $f_i^* phi_i = f_i^* psi_i$, there exists a further stage $i' >= i$ s.t. $f_(i',i)^* phi_i = f_(i',i)^* psi_i$. 
]
#proof[
  See #cite-stacks("01ZR")[Lemma 32.10.2]. 
]

Finally, we study properties on the limit that passes to some finite stage. 

#theorem(name: <passage-to-limit-of-properties>)[
  Let $S = invlim_(i in I) S_i$ be a projective limit of qcqs schemes with affine transition maps, let $0 in I$, and let $f_0: X_0 -> Y_0$ be a morphism of qcqs $S_0$-schemes. Denote by $f_i: X_i -> Y_i$ the base change of $f_0$ along $S_i -> S_0$ for any $i >= 0$, and by $f: X -> Y$ the base change of $f_0$ along $S -> S_0$. 
  
  We say a property $cal(P)$ *descends from the limit*, if whenever $f$ has the property $cal(P)$, there exists some finite stage $0 <= i in I$ s.t. $f_i$ has the property $cal(P)$. Then: 

  + The following properties descend from the limit: 
    1. affine 
    + separated

  + The following properties descend from the limit, whenever $f_0$ is locally of finite type: 
    1. finite
    + closed immersion
    + immersion
    + monomorphism (as in the categorical sense, or equivalently, the diagonal is an isomorphism)
    + proper

  + The following properties descend from the limit, whenever $f_0$ is locally of finite presentation: 
    1. flat
    + finite and locally free (of some degree $d$)
    + smooth (of some relative dimension $d$)
    + etale
    + isomorphism
    + open immersion
    + surjective
    + unramified
]
#proof[
  See #cite-stacks("081C")[Section 32.8] of Stacks Project, containing proofs for all entries but (2e), and #cite-stacks("081F")[Lemma 32.13.1] for (2e). 

  I will prove (3h)(3d) and (3c) myself for self-containment. For (3h), note that: 
  $
    0 = Omega_(X\/Y) = Omega_(X_i\/Y_i)|_X
  $
  where each $Omega_(X_i\/Y_i)$ is a finitely presented quasi-coherent sheaf of $cal(O)_(X_i)$-modules. By @passage-to-limit-of-sheaves (3), the identity $id = 0$ on $Omega_(X\/Y)$ descends to a finite stage, so $Omega_(X_i\/Y_i) = 0$ for some $i$. 

  (3d) follows from (3a) and (3h), since etaleness is just unramifiedness and flatness. 

  For (3c), by @equiv-defns-of-smooth (3), locally around every point of $X$, $f$ factors as $U ->^j AA^d_Y -> Y$ for $j$ etale. We may take $U$ to be an affine open. 

  The open immersion $U -> X$ is of finite presentation. Thus, by @passage-to-limit-of-morphisms (2), there exists some finite stage $i$ s.t. $U -> X$ come from base changing $U_i -> X_i$ for an $S_i$-scheme $U_i$. By increasing $i$, we may assume that $U_i -> X_i$ is an open immersion by (3f). 
  
  Now $j$ is a morphism of finite presentation. Thus, by increasing $i$, we may assume that $j$ comes from base changing an $S_i$-morphism $j_i: U_i -> AA^d_(Y_i)$. By (3c), $j_i$ is etale for sufficiently large $i$. Now: 
  $
    U_i ->^(j_i) AA^d_(Y_i) -> Y_i
  $
  and $f_i|_(U_i)$ both base changes to $f|_U$ in the limit. By @passage-to-limit-of-morphisms (3), they agree upon base changing to a finite stage. Thus, there exists a finite stage $i$ s.t. $f_i|_(U_i)$ is smooth of relative dimension $d$. 

  Since $X$ is qcqs, we may cover it by affine opens with etale charts, and take the upper bound of the finite stages to descend smoothness on these finitely many charts. This concludes the proof of (3c). 
]

#remark[
  There are two major ways to use passage to limit. 

  + Any qcqs scheme is a projective limit of finite type $ZZ$-schemes with affine transition morphisms, according to @absolute-noetherian-approx. This allows us to reduce statements on qcqs schemes to those on finite type $ZZ$-schemes, and in particular noetherian schemes. 

  + $Spec(cal(O)_(X,x)) = invlim_(x in U subset X \ U #[affine]) U$ is a projective limit of affine schemes. This allows us to spread out properties at a single point to an open neighborhood. 

    #example(name: <generic-flatness>)[
      To demonstrate how to use (2), we show that (2) may be used to prove generic flatness: 

      - For any morphism $f: X -> Y$ with $Y$ integral, there exists a nonempty open set $V subset Y$ s.t. $f: f^(-1)(V) -> V$ is flat. 

      Let $eta in Y$ be the generic point. Now $Spec(cal(O)_(Y,eta)) = Spec(K(Y))$ is the spectrum of a field. Therefore, the base change $X_eta -> eta$, i.e. the generic fiber is automatically flat. By passage along the limit: 
      $
        Spec(cal(O)_(Y,eta)) = invlim_(#[affine open] emptyset != V subset Y) V
      $
      there exists a nonempty affine open $V subset Y$ s.t. $f: f^(-1)(V) -> V$ is flat. 
    ]
]
