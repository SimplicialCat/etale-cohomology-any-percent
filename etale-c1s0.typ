#import "void-import.typ": *

In this introduction, we briefly give motivation for developing the theory of etale cohomology. 

#question[
  Let $M$ be a complex manifold. How to study the geometry of $M$? 
  - Metrics;

  - "Linearize" $M$ via cohomology theories: 
    + Betti cohomology $H_B^bullet (M, ZZ)$ can be defined either as singular cohomology, or as a sheaf cohomology of a constant sheaf. 

      This is a topological invariant, and it doesn't care about differential structure and so on. 

    + de Rham cohomology $H^bullet_"dR" (M)$. You can define it as the cohomology of either $C^oo$ or analytic differential forms. On a complex manifold, both definitions agree. 

      These cohomology theories enjoy good properties such as:  

      #theorem[
        #set enum(numbering: "(11a)")
        + (de Rham isomorphism)
          $
            H^*_B (M, ZZ) otimes CC cong H^*_B (M, CC) cong H^*_"dR" (M)
          $
          (This is proved using the holomorphic Poincare lemma.)

        + (Hodge decomposition) If $M$ is a compact Kahler manifold (e.g. projective), then there exists a functorial decomposition: 
        $
          H^n_"dR" (M) cong oplus.big_(p+q=n) underbrace(H^(p,q) (M), (p,q)"-Dolbeault cohomology")
        $
        with complex conjugation on $H^n_"dR" (M)$ acting by $overline(H^(p,q)) = H^(q,p)$. 
      ]
]

#question[
  Are there algebraic analogs to study an algebraic variety? Say $X$ is a smooth algebraic variety over a field $k$. 

  - The first thing is that we have algebraic de Rham cohomology: 
    $
      H^bullet_"dR" (X\/k) := h^bullet (R Gamma(X, cal(O)_X overset(->,d) Omega_(X\/k)^1 overset(->,d) dots.c))
    $
    defined via the algebraic de Rham complex. 
    #theorem[
      (Grothendieck; @cite-grothendieck-de-rham) If $k = CC$, there's a natural map from the algebraic de Rham cohomology of $X$ to the analytic de Rham cohomology of $X(CC)$ regarded as a complex manifold:
      $
        H^*_"dR" (X\/CC) -> H^*_"dR" (X(CC))
      $
      that is an isomorphism of finite dimensional $CC$-vector spaces. 
    ]
    That said, algebraic de Rham cohomology has bad behavior in characteristic $p$. 
    #example[
      Let $X = AA_(FF_p)^1 = Spec(FF_p [x])$. This is an affine space, so higher cohomologies of coherent sheaves vanish. Then: 
      $
        H^bullet_"dR" (X\/FF_p) = h^bullet (#box(baseline: 2em)[
        $
          underbrace(FF_p [x], cal(O)_X (X)) &overset(->, d) underbrace(FF_p [x] d x, Omega_(X\/FF_p)^1 (X))     \ f(x) &|-> f'(x) d x         
        $])
      $
      This map kills not only constants, but also things like $x^p$. Thus $H^0_"dR" (AA^1\/FF_p) = FF_p [x^p]$, an infinite dimensional $FF_p$-vector space. 
    ]
]

#question[
  How about algebraic analogs of $pi_1 (M)$ and Betti cohomology $H^bullet_B (M, ZZ)$? 

  - The answer is the etale cohomology $H^bullet_et (X, underbrace(ZZ_ell "or" QQ_ell, "not" ZZ))$ and the etale fundamental group $pi_1^et (X)$. 

    The following comparison theorem really just says that etale cohomology is a good analog of Betti cohomology for algebraic varieties. 

    #theorem[
      (Artin; @cite-SGA4[Exposé XI, Théorème 4.4]) If $k = CC$, then there exists a natural isomorphism:
      $
        H^n_B (X(CC), ZZ) otimes_ZZ ZZ_ell cong H^n_et (X, ZZ_ell)
      $
      and: 
      $
        pi_1^et (X) cong hat(pi_1^"top" (X(CC)))
      $
      where $pi_1^"top"$ is just the topological fundamental group, and the hat denotes profinite completion: $hat(G) := invlim_(N triangle.l.small G "finite index") G\/N$. 
    ]

    #example[
      $
        H_et^n (AA^1_CC, ZZ_ell) = H_B^n (CC, ZZ_ell) = cases(ZZ_ell&\, n = 0, 0 &\, n!=0) \
        
        pi_1^et (AA^1) = hat(pi_1^"top" (CC)) = 0
      $
      while: 
      $
        pi_1^et (GG_m, 1)  = hat(pi_1^"top" (CC^times)) = hat(ZZ)
      $
      #footnote[Strictly speaking, one should write base points here, and the result is $hat(ZZ)(1)$, which is a Tate twist. You don't need to know what a Tate twist is for now. It will only become relevant some 400 pages later.]
    ]
]

#question[
  How to define $H^bullet_et$ and $pi_1^et$? 

  Note that $pi_1 (M) = Aut(tilde(M)\/M)$ where $tilde(M) -> M$ is the universal covering. This is Galois theory of covering spaces. Thus, we need to perform Galois theory on suitable notions of covering spaces of algebraic varieties. 

  - The first step to algebraize this theory is to define algebraic notions for local isomorphisms. This notion is *etale morphisms*. 

  Etale morphisms will serve as a sort of analog of open subsets of a topological space. Thus, 

  - The etale fundamental group will classify etale covering spaces of an algebraic variety $X$, i.e. finite etale morphisms over $X$; 

  - For a good topological space $X$, singular cohomology can be defined as derived functor cohomology for sheaves on the topological space $X$. 

    Now that etale morphisms, or mnemonically etale opens, are the correct analogs of open sets, we will define the notion of _etale sheaves_. They will be the analog of (topological) sheaves, but with open sets replaced by etale morphisms. Etale cohomology will then be defined as derived functor cohomology for etale sheaves. 
]

The construction of etale cohomology defines a good cohomology theory for algebraic varieties in char $p$. 
#construction[
  Let $X_0$ be a smooth algebraic variety over $k = FF_q$ of char $p$. Define $F_(X_0): X_0 -> X_0$ to be the $q$-th absolute Frobenius, a morphism that is identity on the space level, and acts as $f |-> f^q$ on the sheaf/function level. 

  Now base change to the algebraic closure $X = X_0 times_(FF_q) overline(FF_q)$, so that $F_(X_0)$ base changes to $F = F_(X_0) times id_(Spec(overline(FF_q))): X -> X$, an $overline(FF_q)$ scheme endomorphism. 

  Then for $ell != p$, $F^*$ acts on $H^n_et (X, QQ_ell)$, a finite-dimensional $QQ_ell$-vector space, by functoriality of etale cohomology. $F$ acts on the $overline(FF_q)$-points $X(overline(FF_q))$. One can check that the points fixed by $F^n$ are: 
  $
    (X(overline(FF_q)))^(F^n) = X_0 (FF_(q^n))
  $
  This allows us to count points. 

  #theorem[
    (Grothendieck-Lefschetz trace formula) If $X$ is proper#footnote[This is a technical assumption to avoid compactly supported cohomology.] over $FF_q$, 
    $
      \# X_0 (FF_(q^n)) = \# (X(overline(FF_q)))^(F^n) = sum_(m=0)^(2 dim(X)) (-1)^m tr((F^*)^n\; H^m_et (X, QQ_ell))
    $
    (In fact, etale cohomology vanishes above twice the dimension.)
  ]
  This gives a generating series: 
  $
    sum_(n>=1) (\# X_0 (FF_(q^n)))/n t^n = sum_(m=0)^(2 dim(X)) (-1)^m sum_(n>=1) tr((F^*)^n\; H^m_et (X, QQ_ell))/n t^n
  $
  Now when you see such an expression, you should exponentiate it. Since: 
  $
    exp(sum_(n>=1) (alpha^n t^n)/n) = 1/(1-alpha t)
  $
  RHS exponentiates to: 
  $
    product_(m=0)^(2 dim(X)) det(1-t F^*\;H^m_et (X, QQ_ell))^((-1)^(m+1))
  $
  By elementary analysis, LHS exponentiates to: 
  $
    product_(x in abs(X_0) "closed pt") 1/(1-t^(deg(x)))
  $
  where $deg(x) = [k(x):FF_q]$, $k(x)$ is the residue field at $x$. 
  Now: 
  $
    Z(X_0\/FF_q, t) = product_(x in abs(X_0)) 1/(1-t^deg(x))
  $
  gives a $zeta$-function for $X_0$: 
  $
    Z(X_0\/FF_q, q^(-s)) = product_(x in abs(X_0)) 1/(1-abs(k(x)^(-s)))
  $

  By analyzing the properties of etale cohomology in detail, we will be able to formulate and prove the Weil conjectures. 
  #theorem[
    (Weil conjecture; @cite-deligne-weil1) For $X_0$ smooth and proper,
    $
      P_m (t) := det(1- t F^*\;H^m_et (X, QQ_ell)) in QQ_ell [t]
    $
    lands in $1 + t ZZ[t]$ and is independent of $ell$. 

    Moreover, if we write $P_m (t) = product_i (1 - alpha_(m, i) t)$ in $CC[t]$, then every $abs(alpha_(m,i)) =q^(m\/2)$. 
  ]

  The Weil conjectures should really be thought of as the Riemann hypothesis over a function field, and form a solved analog of the Riemann hypothesis! They have profound applications in analytic number theory, giving optimal cancellation and uncorrelation for families of algebraic exponential sums. Such techniques, known as _applied $ell$-adic cohomology_, have far-reaching uses, such as in Yitang Zhang's proof of bounded prime gaps.#footnote[This use case has been optimized away though, according to my knowledge.]   
]

Etale cohomology also constructs Galois representations.  
#construction[
  Let $X\/k$ be a variety, and $ell != "char"(k)$. Then the absolute Galois group $Gal_k$ acts on $H^n_et (X_(overline(k)), QQ_ell)$, by acting on $overline(k)$ in $X_(overline(k)) = X times_k overline(k)$. 

  This gives an $ell$-adic Galois representation $Gal_k -> GL_n (QQ_ell)$. It is usually hard to construct examples of Galois representations of $k$ (e.g. when $k = QQ$). 

  This is important in Langlands Program. For example, Weil conjecture implies Ramanujan conjecture, by interpreting Fourier coefficients of modular forms as certain traces on etale cohomologies. 
]

As a final bonus, etale cohomology is also related to algebraic de Rham cohomology, via an algebraic analog of the de Rham isomorphism. A theorem from $p$-adic Hodge theory is: 
#theorem[
  (Tsuji, Faltings, Niziol, ..., \~2000) Let $k$ be a finite extension of $QQ_p$, and $X$ be a smooth proper algebraic variety over $k$. There exists a canonical isomorphism: 
  $
    H^n_et (X_(overline(k)), QQ_p) otimes_(QQ_p) B_("dR") cong H^n_"dR" (X\/k) otimes_k B_("dR")
  $
  Here, $B_"dR"$ is Fontaine's de Rham period ring, which is a field containing $overline(k)$ and a $p$-adic analog of $2 pi i$. 
]
