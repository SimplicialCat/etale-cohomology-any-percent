#import "void-import.typ": *

== Local structure of etale morphisms

In this section, we establish explicit (Zariski) local descriptions of etale and smooth morphisms. 

The arguments in this section mostly follow from Stacks Project. 

#definition(name: <defn-standard-etale-morphism>)[
  A *standard etale morphism* is a morphism: 
  $
    Spec((A[T]_(h(T)))/((g(T)))) -> Spec(A)
  $
  for $g(T), h(T) in A[T]$ with $g(T)$ monic and $(g'(T), g(T)) = (1) subset A[T]_(h(T))$. Now the relative differential sheaf of this is: 
  $
    Omega_((A[T]_(h(T))\/g(T))\/A) cong (A[T]_(h(T)) d T)/((g(T), g'(T))) = 0
  $
  Also, since $g(T)$ is monic, $A[T]_(h(T))\/g(T)$ is the localization of a finite free $A$-algebra, hence flat over $A$. Thus, a standard etale morphism is necessarily etale. 
]

#theorem(name: <local-struct-of-etale-morphisms>)[
  (Local structure of etale morphisms) For any morphism $f: X -> Y$ etale at $x$ with $y = f(x)$, there exist affine opens $x in U = Spec(B) subset X$, $y in V = Spec(A) subset Y$ s.t. $f(U) subset V$ and $f: Spec(B) -> Spec(A)$ is isomorphic to a standard etale morphism. 
]
#proof[
  Since etaleness is local on base and source, by shrinking $X, Y$ around $x, y$, we may assume that $X = Spec(B), Y = Spec(A)$ are affine. Etaleness is local on source, so we may shrink $X, Y$ appropriately to assume that $f$ is etale. 

  Now $f$ is of finite presentation, so by @absolute-noetherian-approx, @passage-to-limit-of-morphisms and @passage-to-limit-of-properties (3d), we may assume that $f$ comes from base changing an etale morphism $f_0: X_0 -> Y_0$ where $X_0, Y_0$ are affine schemes of finite type over $ZZ$. Base changing a standard etale along an affine morphism still gives a standard etale. Thus, we may replace $f$ with $f_0$ and assume that $X, Y$ are of finite type over $ZZ$ too, in particular noetherian. 

  Step 1. Produce an immersion $X -> AA^1_Y$ by appropriately choosing a function $b in B$. 
  
  #proof[
    Since etale morphisms are quasi-finite, by Zariski main theorem, we may factor $f$ as: 
    $
      X = Spec(B) ->^j Z = Spec(C) ->^(ol(f)) Y = Spec(A)
    $
    with $j$ an open immersion and $ol(f)$ finite. Replacing $f$ with $ol(f)$, we may assume that $f$ is finite and etale at $x$ (and drop the assumption that $f$ is globally etale). Let $x in X, y in Y$ correspond to prime ideals $frak(q) subset B, frak(p) subset A$. Now consider the fiber $X_y$, being the spectrum of: 
    $
      B otimes_A k(y) = product_(i=1)^m T_i
    $
    Here, $B otimes_A k(y)$ is finite over $k(y)$, hence artinian, and is a product of artinian local rings $T_i$. Each point in the fiber $X_y$ corresponds to one direct factor, so let $x in X_y$ correspond to the factor $T_1$. Put $X_y = {x = x_1, x_2, dots.c, x_m}$. 
    
    Since $f$ is etale at $x$, $T_1 = k(x)$ is a field and a finite separable extension of $k(y)$. Pick a primitive element $alpha != 0$ of $k(x)\/k(y)$, and consider the element: 
    $
      beta = (underbrace(alpha, in T_1 = k(x)), underbrace(0, in T_2), dots.c, underbrace(0, in T_m)) in B otimes_A k(y) = product_(i=1)^m T_i
    $
    Now $B otimes_A k(y) = B_(frak(p))\/frak(p) B_(frak(p))$, so $beta = b mod frak(p) B_(frak(p))$ for some $b in B_(frak(p))$. We clear the denominator of $B$ by multiplying $beta$ by a suitable element of $A - frak(p)$, which boils down to multiplying $alpha$ by a nonzero element of $k(y)$. This does not change the facts that $0 != alpha$ and $k(x) = k(y)(alpha)$. Lift $beta$ to $b in B$, and we have defined a factorization: 
    $
      A -> A[T] -->^("ev"_b) B
    $
    or a factorization $Spec(B) ->^h Spec(A[T]) ->^p Spec(A)$ of $f$. Take $I = ker("ev"_b) subset A[T]$ an ideal, and $A[b] = im("ev"_b) subset B$ a subring. We in fact have a factorization: 
    $
      Spec(B) -> Spec(A[b]) cong Spec(A[T]\/I) -> Spec(A[T]) -> Spec(A)
    $
    Here, $I$ contains a monic polynomial since $B$ is finite over $A$. 

    We claim that $Spec(B) -> Spec(A[T]\/I)$ is an open immersion near $x$. Put $D = A[b] cong A[T]\/I$, and let $frak(r) in Spec(D)$ be the image of $x = frak(q) in Spec(B)$ (also identified as a prime ideal $frak(r) subset A[T]$ containing $I$). $B$ is finite over $A$, hence over $D$. 
    
    We need to check that $B_(frak(q)) cong D_(frak(r))$. Now: 

    - Note that $frak(q) in Spec(B)$ is the only prime lying above $frak(r) in Spec(D)$. Indeed, any prime $x' = frak(q)' in Spec(B)$ above $frak(r)$ must lie above $y = frak(p) in Spec(A)$, thus correspond to a point in $X_y$. This point $x' = x_i$ corresponds to a factor $T_i$ in $B otimes_A k(y) = product_(i=1)^m T_i$. If $i >= 2$, $x_i$ lies above the prime ideal: 
      $
        ker(A[T] -->^("ev"_b) B\/frak(m)_(x_i) B) in Spec(A[T])
      $
      This ideal contains $T$ since $b |-> 0 in T_i$. Meanwhile, $ker(A -> B\/frak(m)_(x_i) B)$ is $frak(p)$ since $x_i$ lies above $y = frak(p)$. Thus, this kernel is exactly $(frak(p), T)$. In summary, $x_2, dots.c, x_m$ all lie above the prime ideal $(frak(p), T) subset A[T]$. 

      On the other hand, $b in.not frak(m)_x$ since it reduces to $0 != alpha$ in its residue field. Thus $x = frak(q)$ lies above a prime of $A[T]$ not containing $T$. This completes the proof that $x = frak(q) in Spec(B)$ is the only prime lying above $frak(r) in Spec(D)$. 

    - $B_(frak(r))$ is finite over $D_(frak(r))$ and has going-up. Thus, maximal ideals of $B_(frak(r))$ lie above maximal ideals of $D_(frak(r))$. Since only one prime of $B$ lies above $frak(r) subset D$, this forces $B_(frak(r))$ to be local with maximal ideal $frak(q) B_(frak(r))$. Thus every element of $B - frak(q)$ is already invertible in $B_(frak(r))$, and $B_(frak(r)) = B_(frak(q))$. 

    - Consider $D_(frak(r)) -> B_(frak(r)) -> k(x)$. Its image contains $k(y)$, and also contains the image of $b$ in $k(x)$, which is $alpha$. Thus this map is surjective. It shows that $k(frak(r)) = k(x)$. Now we have seen $B_(frak(r)) = B_(frak(q))$, which says: 
      $
        D_(frak(r))\/frak(r) D_(frak(r)) = B_(frak(r))\/frak(r) B_(frak(r))
      $
      under the injective finite map $D_(frak(r)) -> B_(frak(r))$. This says that $B_(frak(r)) = D_(frak(r)) + frak(r) B_(frak(r))$, and Nakayama's lemma applied to $B_(frak(r))\/D_(frak(r))$ gives $D_(frak(r)) = B_(frak(r)) = B_(frak(q))$. 

    - Since $D_(frak(r)) = B_(frak(r))$, by spreading out (maybe @passage-to-limit-of-morphisms (3)), there exists a function $u in D$ s.t. $D_u = B_u$. 

    Thus, shrinking $Spec(B)$ to $Spec(B_u)$, we have an open immersion $Spec(B) -> Spec(A[T]\/I)$. By shrinking $B$ further, we may assume that $B$ is a principal affine open of $Spec(A[T]\/I)$. That is, there exists a polynomial $h(T) in A[T]$ s.t: 
    $
      B cong A[T]_(h(T))\/I
    $
    Finally, recall that $I$ contains a monic polynomial. 
    #suppress-qed
  ]

  Thus, by shrinking $B$, we may assume that: 
  $
    B = (A[T]\/I)_(h(T))
  $
  has $Spec(B) -> Spec(A)$ etale, with $h(T) in A[T]$, and $I subset A[T]$ being an ideal containing a monic polynomial in $A[T]$ that does not contain $h(T)$. 

  Step 2. Reduce $I$ to one monic relation. 

  #proof[
    Since $B\/A$ is etale, 
    $
      0 = Omega_(B\/A) = Omega_((A[T]\/I)\/A) otimes_(A[T]\/I) B = (B d T)/((d f: f in I))
    $
    Thus, we may pick $G(T) in I$ s.t. $d G in B^times d T$. That is, $G'(T) in A[T]$ maps to a unit in $B$. 

    Now choose a monic relation $P(T) in I$ and choose $N >= 2$ so large that $N deg(P(T)) > deg(G(T))$. Then: 
    $
      g(T) = P(T)^N + G(T) in I
    $
    is monic and has $g'(T) = N P(T)^(N-1) P'(T) + G'(T)$. Now $P(T) in I$ is sent to $0$ in $B$, so $g'(T)$ and $G'(T)$ have the same image in $B$, a unit. Thus $g(T) in I$ is a monic relation with $g'(T) in B^times$. We have a surjection: 
    $
      A[T]_(h(T))\/g(T) -> A[T]_(h(T))\/I = B
    $
    sending $g'(T)$ to an element of $B^times$. Thus it factors through $A[T]_(h(T)g'(T))\/g(T)$. 

    Now factor $f$ as: 
    $
      Spec(B) = Spec(A[T]_(h(T))\/I) ->^i Spec(A[T]_(h(T)g'(T))\/g(T)) ->^(f') Spec(A)
    $
    Here, $f'$ is a standard etale morphism, hence etale (since $g'(T)$ is invertible in $A[T]_(h(T)g'(T))\/g(T)$), and $f$ is etale. Thus the closed immersion $i$ is in fact etale. It is thus an open and closed immersion. Thus $Spec(B)$ is a standard affine open of $Spec(A[T]_(g'(T)h(T))\/g(T)) = Spec((A[T]\/g(T))_(g'(T)h(T)))$ and is obtained by inverting an idempotent that we shall multiply to $g'(T)h(T)$. Thus $Spec(B) -> Spec(A)$ is standard etale. 
    #suppress-qed
  ]
  This proves the local structure of etale morphisms. 
]

// The next goal is to establish a local structure theorem for smooth morphisms. Recall the definition (as in Hartshorne) that: 

// - A morphism $f: X -> Y$ of finite presentation is said to be *smooth (of relative dimension $d$)* at $x$, if it is flat at $x$ and $(Omega_(X\/Y))_x$ is free (of rank $d$). 

//   A morphism $f: X -> Y$ is said to be *smooth (of relative dimension $d$)*, if it is smooth at every point. Equivalently, if $f$ is flat and $Omega_(X\/Y)$ is locally free (of rank $d$). 

// Thus under this definition, etale morphisms are precisely smooth morphisms of relative dimension $0$. A discussion on smooth morphisms should be referred to Hartshorne, Section 3.10. 

// #definition[
//   A morphism $f: X -> Y$ is said to be *standard smooth* of relative dimension  $d$, if it factors as: 
//   $
//     X ->^j AA^d_Y -> Y
//   $
//   for an etale morphism $j$. A standard smooth morphism of relative dimension $d$ is smooth of relative dimension $d$, since etale morphisms are smooth of relative dimension $0$, and $AA^d_Y -> Y$ is smooth of relative dimension $d$, and smooth morphisms composes. 
// ]

// #theorem(name: <local-struct-of-smooth-morphisms>)[
//   (Local structure of smooth morphisms) For any morphism $f: X -> Y$ smooth of relative dimension $d$ at $x in X$, there exists an open neighborhood $x in U subset X$ s.t. $U -> Y$ is standard smooth. 
// ]
// #proof[
//   Since $Omega_(X\/Y)$ is locally free of rank $d$ at $x$, by shrinking $X$ around $x$, we may assume that $X = Spec(B)$ is affine and $Omega_(X\/Y)$ is free of rank $d$. We may shrink $X$ further to assume that the image of $X$ is contained in an affine open $U subset Y$. Now if we have an etale chart $X -> AA^d_U$, the open immersion gives an etale chart $X -> AA^d_Y$. Thus it is safe to replace $Y$ with $U$ and assume that $Y = Spec(A)$ is affine too. Now that we have an isomorphism $Omega_(B\/A) cong B^(oplus d)$, we may pick $b_1, dots.c, b_d in B$ s.t. $d b_1, dots.c, d b_d$ forms a basis of $Omega_(B\/A)$. These sections define a map: 
//   $
//     Spec(B) -> Spec(A[T_1, dots.c, T_d])
//   $ 
//   by evaluating $T_i$ to $b_i$. We thus have the first exact sequence: 
//   $
//     Omega_(A[T_1,dots.c,T_d]\/A) otimes_(A[T_1,dots.c,T_d]) B -> Omega_(B\/A) -> Omega_(B\/A[T_1,dots.c,T_d]) -> 0
//   $
//   Now $Omega_(A[T_1,dots.c,T_d]\/A) otimes_(A[T_1,dots.c,T_d]) B cong B d T_1 oplus dots.c oplus B d T_d$, and the first map sends $d T_i |-> d b_i$. By our choice of the $b_i$'s, this map is an isomorphism. Thus $Omega_(B\/A[T_1,dots.c,T_d]) = 0$ and so $B$ is unramified over $A[T_1, dots.c, T_d]$. It suffices to show that it is flat. By fiberwise criterion for flatness (#cite-stacks("039E")[Lemma 37.16.4]), it suffices to check that for each point $y in Spec(A)$, the base change: 
//   $
//     X_y = Spec(B otimes_A k(y)) -> AA^d_(k(y))
//   $
//   is flat. Now let $x in X_y$ be a closed point sent to a closed point $u in AA^d_(k(y))$: 

//   - $X_y$ is geometrically regular (hence regular) for being smooth over the field $k(y)$, and $AA^d_(k(y))$ is obviously regular. Thus $cal(O)_(X_y,x)$ and $cal(O)_(AA^d_(k(y)),u)$ are regular local rings. 

//   - $dim(cal(O)_(AA^d_(k(y)),u)) = d$. $X_y$ being smooth of relative dimension $d$ over $k(y)$ has pure dimension $d$, and so $dim(cal(O)_(X_y,x)) = d$. Finally, the fiber: 
//     $
//       cal(O)_(X_y,x)\/frak(m)_u cal(O)_(X_y,x) cong k(x)
//     $
//     since $X_y -> AA^d_(k(y))$ is unramified (by definition), and is $0$-dimensional. Thus: 
//     $
//       dim(cal(O)_(AA^d_(k(y)),u)) + dim(cal(O)_(X_y,x)\/frak(m)_u cal(O)_(X_y,x)) = dim(cal(O)_(X_y,x))
//     $

//   By miracle flatness (#cite-stacks("00R4")[Lemma 10.128.1]), $cal(O)_(X_y,x)$ is flat over $cal(O)_(AA^d_(k(y)),u)$. Thus $X_y -> AA^d_(k(y))$ is flat at every closed point of $X_y$. Since the flat locus is open, this map is flat. We are thereby done. 
// ]

Combining the local structure for etale and smooth morphisms, we have the following corollary: 

#corollary[
  For any morphism $f: X -> Y$ smooth of relative dimension $d$ at $x in X$ with $y = f(x)$, by suitably shrinking $X$ around $x$ to $Spec(B)$ and $Y$ around $y$ to $Spec(A)$, we can have: 
  $
    B cong (A[X_1, dots.c, X_d, T]_(h(X,T)))/((g(X,T)))
  $
  s.t. $(g(X, T), partial_T g(X, T)) = (1)$ as an ideal of $A[X_1, dots.c, X_d, T]_(h(X,T))$. 
]
