#import "void-import.typ": *

In this appendix, we prove a few auxiliary results governing the interaction between strict henselization and quasi-finite maps. This will turn out to be very useful in the theory of local acyclicity. 

This appendix mostly follows the development of #cite-stacks("0GIN")[Section 10.156]. 

#lemma(name: <strict-hs-and-qfinite>)[
  (#cite-stacks("05WR")[Lemma 10.156.3]) Let $A -> B$ be a ring map, and let $frak(q) in Spec(B)$ lie above $frak(p) in Spec(A)$. Suppose that $Spec(B) -> Spec(A)$ is quasi-finite at $frak(q)$. Fix a separable closure $k(frak(q)) arrow.r.hook k(frak(q))^sep$, and let $k(frak(p))^sep$ be the separable closure of $k(frak(p))$ in $k(frak(q))^sep$. Take strict henselizations w.r.t. these separable closures. 
  
  Let: 
  $
    frak(r) = ker(A_(frak(p))^#[sh] otimes_(A_(frak(p))) B_(frak(q)) -> k(frak(p))^sep otimes_(k(frak(p))) k(frak(q)) -> k(frak(q))^sep)
  $
  Then there exists a canonical isomorphism: 
  $
    (A_(frak(p))^#[sh] otimes_(A_(frak(p))) B_(frak(q)))_(frak(r)) cong B_(frak(q))^#[sh]
  $
  with $A_(frak(p))^#[sh] -> B_(frak(q))^#[sh]$ finite. 
]
#proof[
  Quasi-finiteness at $frak(q)$ implies that $k(frak(q))\/k(frak(p))$ is finite. Hence $k(frak(p))^sep$ is a separable closure of $k(frak(p))$. 
  
  Moreover, the composite field $k(frak(q)) k(frak(p))^sep subset k(frak(q))^sep$ is finite, hence purely inseparable, over the separably closed field $k(frak(p))^sep$. It is therefore separably closed. Since it is also separable over $k(frak(q))$, it equals $k(frak(q))^sep$. Thus $k(frak(q))^sep\/k(frak(p))^sep$ is finite and purely inseparable, and the map: 
  $
    k(frak(p))^sep otimes_(k(frak(p))) k(frak(q)) -> k(frak(q))^sep
  $
  is surjective.

  Put $R = A_(frak(p))^#[sh]$ and $C = R otimes_(A_(frak(p))) B_(frak(q))$. Quasi-finiteness is preserved by base change, so $C$ is quasi-finite over $R$ at $frak(r)$. By Zariski's main theorem, an open neighborhood $U subset Spec(C)$ of $frak(r)$ admits an open immersion into a scheme $ol(U)$ finite over $Spec(R)$. 
  
  Since $R$ is henselian, by @equiv-defns-of-henselian (1), $ol(U)$ decomposes into spectra of finite local $R$-algebras. The point $frak(r)$ is the closed point of one such component $V$. Now $U inter V$ contains the closed point of the local scheme $V$, hence $U inter V = V$. Consequently,
  $
    C_(frak(r)) cong cal(O)_(V,frak(r))
  $
  is a finite local $R$-algebra. It is thus strict henselian by @finite-over-henselian-is-henselian. By the surjectivity of $k(frak(p))^sep otimes_(k(frak(p))) k(frak(q)) -> k(frak(q))^sep$, the residue field of $C_(frak(r))$ is $k(frak(q))^sep$, so $C_(frak(r))$ is strictly henselian.

  The local map $B_(frak(q)) -> C_(frak(r))$ is compatible with the chosen residue-field inclusion, so the universal property of strict henselization gives a unique local map: 
  $
    B_(frak(q))^#[sh] -> C_(frak(r))
  $
  Conversely, the compatible maps $R -> B_(frak(q))^#[sh]$ and $B_(frak(q)) -> B_(frak(q))^#[sh]$ induce a map $C -> B_(frak(q))^#[sh]$. The inverse image of the maximal ideal is $frak(r)$ by its definition, so this map localizes to: 
  $
    C_(frak(r)) -> B_(frak(q))^#[sh].
  $
  Their composition on $B_(frak(q))^#[sh]$ is the identity by the uniqueness in its universal property. Their composition on $C_(frak(r))$ is the identity because it is a $C$-algebra map from a localization of $C$ to itself. Thus these two maps invert each other, and are canonical isomorphisms. Finally, $A_(frak(p))^#[sh] -> B_(frak(q))^#[sh]$ is finite, since $C_(frak(r))$ is finite over $R$ as argued above. 
]

#lemma(name: <tensor-of-local-rings-still-local-criterion>)[
  (#cite-stacks("092Y")[Lemma 10.156.5]) Let $A -> B$ and $A -> C$ be local homomorphisms of local rings, s.t:: 

  - $A -> C$ is integral; 

  - Either $k(B)\/k(A)$ or $k(C)\/k(A)$ is purely inseparable. 

  Then $D = B otimes_A C$ is a local ring and $B -> D$, $C -> D$ are both local homomorphisms. 
]
#proof[
  Note that:
  $
    D\/frak(m)_B D cong k(B) otimes_A C cong k(B) otimes_(k(A)) C\/frak(m)_A C
  $
  Since $C$ is local and integral over $A$, $Spec(C\/frak(m)_A C)$ is local and integral over the field $k(A)$. By going up it is $0$-dimensional, and is thus the single point $frak(m)_C\/frak(m)_A C$. 
  
  Thus, $k(C) = (C\/frak(m)_A C)_#[red]$, and so $Spec(D\/frak(m)_B D)$ is homeomorphic to $Spec(k(B) otimes_(k(A)) k(C))$. Since one of $k(B)\/k(A)$ and $k(C)\/k(A)$ is purely inseparable, $Spec(k(B) otimes_(k(A)) k(C))$ is a point. Thus $Spec(D\/frak(m)_B D)$ is a single point. 

  The map $B -> D$ is integral as the base change of the integral map $A -> C$. Hence, by going up, every maximal ideal of $D$ lies above $frak(m)_B$. But $Spec(D\/frak(m)_B D)$ is a point. Thus $D$ has only one maximal ideal, and so $D$ is local with $frak(m)_D$ lying above $frak(m)_B$. Furthermore, $D\/frak(m)_B D cong k(B) otimes_(k(A)) C\/frak(m)_A C$, where $frak(m)_D$ is the only point on the left, and $frak(m)_C$ is the only point on the right. Thus $frak(m)_D$ lies above $frak(m)_C$, and so $B -> D$ and $C -> D$ are local homomorphisms. 
]

#lemma(name: <strict-henselizations-tensors-and-qfinites>)[
  Suppose that $B, C$ are $A$-algebras, $D = B otimes_A C$ and $Omega$ is a separably closed field. Given a ring homomorphism $psi_D: D -> Omega$, we may compose to get $psi_A, psi_B, psi_C$ from $A,B,C$ to $Omega$, respectively. Let $frak(p)_(A,B,C,D)$ be $ker(psi_(A,B,C,D))$ respectively, being prime ideals of the respective rings. These ideals lie above each other. The canonical map: 
  $
    B_(frak(p)_B)^#[sh] otimes_(A_(frak(p)_A)^#[sh]) C_(frak(p)_C)^#[sh] -> D_(frak(p)_D)^#[sh]
  $
  is an isomorphism if $B_(frak(p)_B)$ is a filtered colimit of quasi-finite $A_(frak(p)_A)$-algebras. This includes the cases: 

  - $A -> B$ is quasi-finite at $frak(p)_B$;
  
  - $B$ is a filtered colimit of quasi-finite $A$-algebras. In particular, when $B$ is integral over $A$. 

  (Here, all strict henselizations of $A,B,C,D$ are taken w.r.t. the separable closure of $k(frak(p)_(A,B,C,D))$ in $Omega$.)
]
#proof[
  We may replace $A, B, C$ with $A_(frak(p)_A), B_(frak(p)_B), C_(frak(p)_C)$ respectively, to assume that $A, B, C$ are local rings, the structure maps $A -> B, A -> C$ are local homomorphisms, and $frak(p)_(A,B,C) = frak(m)_(A,B,C)$. 

  Since strict henselizations are compatible with filtered colimits (@henselization-and-directed-limits and also @artin-mazur-construction) and so are tensors, we may assume that $B$ is a quasi-finite $A$-algebra. 

  Consider the canonical map: 
  $
    B^#[sh] otimes_(A^#[sh]) C^#[sh] -> D_(frak(p)_D)^#[sh]
  $
  By @strict-hs-and-qfinite, since $B$ is quasi-finite over $A$, 
  $
    B^#[sh] cong (A^#[sh] otimes_A B)_(ker(A^#[sh] otimes_A B -> Omega))
  $
  and since $D$ is quasi-finite over $C$ by base change, by @strict-hs-and-qfinite too, 
  $
    D_(frak(p)_D)^#[sh] cong (C^#[sh] otimes_C D)_(ker(C^#[sh] otimes_C D -> Omega))
  $
  Now by definition $C^#[sh] otimes_C D cong C^#[sh] otimes_A B$. Now: 
  $
    B^#[sh] otimes_(A^#[sh]) C^#[sh] cong (C^#[sh] otimes_A B)_(ker(A^#[sh] otimes_A B -> Omega))
  $
  Thus, both sides of the canonical homomorphism $B^#[sh] otimes_(A^#[sh]) C^#[sh] -> D_(frak(p)_D)^#[sh]$ are compatibly localizations of the same ring $C^#[sh] otimes_A B$. To show that it is an isomorphism, it suffices to show that both sides are local. 
  
  Thus it suffices to show that $B^#[sh] otimes_(A^#[sh]) C^#[sh]$ is local. By @strict-hs-and-qfinite, $A^#[sh] -> B^#[sh]$ is finite with purely inseparable residue field extension. Thus by @tensor-of-local-rings-still-local-criterion, $B^#[sh] otimes_(A^#[sh]) C^#[sh]$ is local, and we are done. 
]
