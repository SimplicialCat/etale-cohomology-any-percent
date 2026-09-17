#import "void-import.typ": *

#let index-entry(name, qualifier: none, loc) = {
  ((
    name: name, 
    qualifier: qualifier, 
    loc: loc
  ),)
}
#let make-index(index-entries) = {
  let entries-by-name = (:)
  for entry in index-entries {
    let known-entries = entries-by-name.at(repr(entry.name), default: ())
    known-entries.push((
      name: entry.name, 
      qualifier: entry.qualifier, 
      loc: query(entry.loc).map(it => numbering("1", ..counter(page).at(it.location()))).at(0, default: "-999")
    ))
    entries-by-name.insert(repr(entry.name), known-entries)
  }
  // todo: replace repr() with a more sensible function
  for (_, entries) in entries-by-name.pairs().sorted(key: arr => { let (name, _) = arr; name }) {
    let name = entries.at(0).name
    let head-loc = entries.filter(entry => entry.qualifier == none).map(entry => entry.loc).at(0, default: none)
    let qualified-locs = entries.filter(entry => entry.qualifier != none).sorted(key: entry => repr(entry.qualifier))
    
    [#name#if (head-loc != none) [#h(0.5em)#box(width: 1fr, repeat[.])#h(0.5em)#head-loc]#linebreak()]
    

    for entry in qualified-locs {
      [#h(1.5em)#entry.qualifier#h(0.5em)#box(width: 1fr, repeat[.])#h(0.5em)#entry.loc#linebreak()]
    }
  }
}

#pagebreak()
#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9009)
  [= Index]
  columns(2, {context make-index({
    // Section 2.1: Unramified, etale and smooth morphisms
    index-entry([Kahler differentials], qualifier: [$Omega_(X\/Y)$], <kahler-differentials>)
    index-entry([unramified morphism], <defn-unramified-and-etale-morphisms>)
    index-entry([etale morphism], <defn-unramified-and-etale-morphisms>)
    index-entry([Kummer covering], <kummer-and-artin-schreier-coverings>)
    index-entry([Artin-Schreier covering], <kummer-and-artin-schreier-coverings>)
    index-entry([Jacobian criterion], qualifier: [for etaleness], <jacobian-criterion-for-etaleness>)
    index-entry([smooth morphism], <defn-smooth-morphisms>)

    // Section 2.2: Local structure of etale morphisms
    index-entry([etale morphism], qualifier: [standard], <defn-standard-etale-morphism>)

    // Section 2.3: Infinitesimal lifting criterion
    index-entry([formally smooth morphism], <defn-formal-morphisms>)
    index-entry([formally unramified morphism], <defn-formal-morphisms>)
    index-entry([formally etale morphism], <defn-formal-morphisms>)
    index-entry([infinitesimal lifting criterion], <infinitesimal-lifting-criterion>)

    // Section 2.4: Fpqc descent
    index-entry([faithfully flat morphism], <defn-faithfully-flat-and-fpqc-morphisms>)
    index-entry([fpqc morphism], <defn-faithfully-flat-and-fpqc-morphisms>)
    // index-entry([base-change notation], qualifier: [$X', X'', X'''$], <descent-notation>)
    // index-entry([Cech nerve notation], qualifier: [$S'', S'''$], <descent-notation>)
    index-entry([canonical descent datum], <descent-data>)
    index-entry([descent datum], qualifier: [$"DD"(f)$], <descent-data>)
    index-entry([Amitsur sequence], <amitsur-complex-exact>)

    // Section 2.5: Henselizations & strict henselizations
    index-entry([henselian local ring], <defn-henselian-local-rings>)
    index-entry([strictly henselian local ring], <defn-henselian-local-rings>)
    index-entry([henselization], qualifier: [$A^#[h]$], <defn-henselizations>)
    index-entry([strict henselization], qualifier: [$A^#[sh]$], <defn-henselizations>)

    // Section 2.A1: Radicial morphisms
    index-entry([radicial morphism], <defn-radicial-morphism>)
    index-entry([universal homeomorphism], <radicial-morphism-first-props>)

    // Section 3.1: Etale covering spaces
    index-entry([etale cover], <terminology-etale-coverings>)
    index-entry([finite etale covering space], qualifier: [$FEt_X$], <terminology-etale-coverings>)
    index-entry([geometric point], <defn-geometric-points>)
    index-entry([pointed scheme], <defn-geometric-points>)
    index-entry([fiber functor], <defn-fiber-functor>)

    // Section 3.2: Galois covering spaces
    index-entry([Galois covering space], <defn-galois-covering-space>)
    index-entry([Galois closure], <galois-closure-exists>)
    index-entry([quotient], qualifier: [by a finite group], <defn-quotient-by-finite-group>)
    index-entry([admissible action], <defn-admissible-group-action>)
    index-entry([inertia group], qualifier: [$I_(G)(z)$], <defn-inertia-group>)

    // Section 3.3: Etale fundamental group
    index-entry([etale fundamental group], qualifier: [$pi_(1)^(et)(X, ol(x))$], <defn-etale-fundamental-group>)
    index-entry([profinite group], qualifier: [etale fundamental group], <pi1et-as-invlim>)

    // Section 4.1: Sites
    index-entry([site], <defn-site>)
    index-entry([presheaf], <defn-presheaves-and-sheaves-on-sites>)
    index-entry([sheaf], <defn-presheaves-and-sheaves-on-sites>)
    index-entry([etale site], qualifier: [$X_"et"$], <defn-etale-site>)
    index-entry([etale sheaf], <defn-etale-site>)

    // Section 4.3: Sheaf cohomology
    index-entry([Cech cohomology], qualifier: [zeroth], <constr-zeroth-cech-cohom>)
    index-entry([sheafification], qualifier: [$(-)^\#$], <defn-sheafification>)
    index-entry([constant sheaf], qualifier: [$ul(M)_X$], <detection-and-const-sheaf>)
    index-entry([etale cohomology], qualifier: [$H^(bullet)_(et)(X, -)$], <defn-etale-cohomology>)

    // Section 4.4: Derived functors
    index-entry([direct image], qualifier: [$f_*$], <defn-etale-direct-image>)
    index-entry([inverse image], qualifier: [$f^(-1)$], <defn-etale-sheaf-inverse-image>)
    index-entry([higher direct image], qualifier: [$R^q f_*$], <defn-higher-direct-image>)
    index-entry([spectral sequence], qualifier: [Leray], <derived-lower-star-first-props>)

    // Section 4.5: Stalks
    index-entry([stalk], <defn-etale-stalk>)
    index-entry([germ], <defn-germs-and-support>)
    index-entry([support], <defn-germs-and-support>)
    index-entry([Godement resolution], <injective-godement-resolution>)

    // Section 4.6: Cech cohomology
    index-entry([Cech cohomology], <constr-cech-cohom>)
    index-entry([spectral sequence], qualifier: [Cech-to-derived-functor], <cech-to-derived-functor-spectral-sequence>)

    // Section 4.7: Open and closed immersions
    index-entry([extension by zero], qualifier: [$f_!$], <etale-lower-shriek-defn>)
    index-entry([exceptional inverse image], qualifier: [$i^!$], <closed-immersion-upper-shriek-constr>)

    // Section 4.8: Torsion sheaves
    index-entry([torsion sheaf], <defn-torsion-sheaf>)
    index-entry([sheaf of $ZZ\/n$-modules], <defn-zn-module-sheaf>)

    // Section 4.9: Internal Hom and tensor
    index-entry([etale sheaf of rings], <defn-etale-ring-and-module-sheaves>)
    index-entry([etale sheaf of modules], <defn-etale-ring-and-module-sheaves>)
    index-entry([internal hom], <defn-internal-hom>)
    index-entry([tensor product], qualifier: [of etale sheaves], <defn-sheaf-tensor-product>)

    // Section 4.A1: Derived category statements
    index-entry([cohomological dimension], <defn-cohomological-dimension>)
    index-entry([derived category], qualifier: [of etale sheaves], <derived-categories-of-etale-sheaves>)
    index-entry([derived category], qualifier: [of torsion etale sheaves], <derived-categories-of-etale-sheaves>)

    // Section 5.1: Limit formulas
    index-entry([limit formula], qualifier: [for sheaves], <limit-formula-for-sheaves>)
    index-entry([limit formula], qualifier: [for schemes], <limit-formula-for-schemes>)
    index-entry([strict localization], qualifier: [$cal(O)_(X, ol(x))$], <strict-local-ring-and-localization>)
    index-entry([strict localization], qualifier: [$tilde(X)_(ol(x))$], <strict-local-ring-and-localization>)
    index-entry([stalk], qualifier: [of a derived direct image], <stalks-of-derived-lowerstar>)

    // Section 5.2: Etale cohomology of quasi-coherent sheaves
    index-entry([etale cohomology], qualifier: [of quasi-coherent sheaves], <etale-cohom-of-qcoh-sheaf>)

    // Section 5.3: H1 of the multiplicative group
    index-entry([multiplicative group], qualifier: [$H^(1)_(et)(X, GG_m) = "Pic"(X)$], <h1-of-gm-is-pic>)

    // Section 5.4: H1 of a constant sheaf
    index-entry([etale torsor], <defn-etale-g-torsor>)
    index-entry([etale torsor], qualifier: [pointed], <defn-etale-g-torsor>)
    index-entry([torsor classification], qualifier: [by the etale fundamental group], <hom-from-pi1-classifies-torsors>)
    index-entry([torsor classification], qualifier: [by $caron(H)^1$], <cech-h1-classifies-torsors>)

    // Section 5.5: Topological invariance
    index-entry([topological invariance], <top-invariance>)

    // Section 5.6: The etale site of a field
    index-entry([etale site], qualifier: [of a field], <struct-of-spec-k-et>)
    index-entry([Galois cohomology], <galois-cohom-props>)

    // Section 5.7: Etale cohomology of curves
    index-entry([divisor exact sequence], <divisor-exact-sequence>)
    index-entry([etale cohomology], qualifier: [of curves], <cohom-of-general-curve>)

    // Section 6.1: Proper base change setup
    index-entry([base change morphism], qualifier: [$g^(-1) R^q f_* -> R^q f'_* g'^(-1)$], <base-change-constr>)
    index-entry([proper base change theorem], <proper-base-change>)

    // Section 6.2: Constructible sheaves
    index-entry([locally constant sheaf], <defn-locally-constant-and-lcc-sheaves>)
    index-entry([locally constant constructible sheaf], qualifier: [l.c.c. sheaf], <defn-locally-constant-and-lcc-sheaves>)
    index-entry([generalization], qualifier: [of a geometric point], <defn-specialization-morphism>)
    index-entry([specialization morphism], qualifier: [$sp_(ol(x), ol(eta))$], <defn-specialization-morphism>)
    index-entry([representable etale sheaf], qualifier: [$h_Y$], <representable-etale-sheaf>)
    index-entry([constructible sheaf], <defn-constructible-sheaf>)
    index-entry([derived category], qualifier: [of constructible etale sheaves], <constructible-derived-categories>)

    // Section 6.7: Proof of Seed
    index-entry([Grothendieck existence theorem], <grothendieck-existence-thm>)

    // Section 6.8: Higher vanishing
    index-entry([etale cohomological dimension], qualifier: [$cd(X)$], <etale-cohomological-dimension>)
    index-entry([vanishing theorem], qualifier: [Artin], <artin-vanishing>)
    index-entry([vanishing theorem], qualifier: [Grothendieck], <grothendieck-vanishing>)
    index-entry([vanishing theorem], qualifier: [relative Artin], <relative-artin-grothendieck-vanishing>)
    index-entry([vanishing theorem], qualifier: [relative Grothendieck], <relative-artin-grothendieck-vanishing>)

    // Section 6.A1: Derived category statements
    index-entry([proper base change theorem], qualifier: [derived], <derived-base-changes>)

    // Section 7.1: Construction of Rf! and compactly supported cohomology
    index-entry([Nagata compactification], <nagata-compactification>)
    index-entry([compactification], qualifier: [of a morphism], <defn-compactification>)
    index-entry([derived pushforward with proper support], qualifier: [$R f_!$], <defn-derived-pushforward-with-proper-support>)
    index-entry([cohomology with proper support], qualifier: [$R Gamma_(c)(X, -)$], <defn-cohomology-with-proper-support>)
    index-entry([higher direct image with proper support], qualifier: [$R^q f_!$], <proper-support-cohomology-notation>)
    index-entry([cohomology with proper support], qualifier: [$H^(q)_(c)(X, -)$], <proper-support-cohomology-notation>)

    // Section 7.3: Projection and Kunneth formulas
    index-entry([projection formula], <projection-formula>)
    index-entry([Kunneth formula], <kunneth-formula>)

    // Section 8.1: General reduction on base changes
    index-entry([derived category], qualifier: [$D^(b)_(#[ctf])(X_et, Lambda)$], <constructible-finite-tor-derived-category>)
    index-entry([relative base change morphism], <relative-base-change-constr>)

    // Section 8.2: Local acyclicity
    index-entry([vanishing cycle variety], qualifier: [$F_(ol(x), ol(t))$], <defn-local-acyclicity>)
    index-entry([local acyclicity], <defn-local-acyclicity>)
    index-entry([universal local acyclicity], <defn-local-acyclicity>)
    index-entry([cospecialization map], qualifier: [$"cosp"$], <cospecialization-map>)

    // Section 8.3: Smooth base change
    index-entry([smooth base change theorem], <smooth-base-change>)

    // Section 8.4: Finiteness of Rf!
    index-entry([finiteness theorem], qualifier: [for derived pushforward with proper support], <finiteness-of-lower-shriek>)

    // Section 9.1: Trace map of a smooth morphism
    index-entry([trace map], qualifier: [$Tr_(X\/Y)$], <existence-of-trace-map>)
    index-entry([Tate twist], qualifier: [$cal(K)(m)$], <defn-tate-twists>)

    // Section 9.2: Poincare duality
    index-entry([cup product pairing], qualifier: [$smile$], <defn-cup-product-pairing>)
    index-entry([exceptional inverse image], qualifier: [$R f^!$], <existence-of-upper-shriek>)
    index-entry([purity map], qualifier: [$t_(X\/Y)$], <purity-map>)
    index-entry([Poincare duality], qualifier: [relative], <relative-poincare-duality>)
    index-entry([Poincare duality], qualifier: [absolute], <absolute-poincare-duality>)
    index-entry([purity], qualifier: [relative], <relative-purity>)

    // Section 9.3: Generic base change and finiteness
    index-entry([generic base change theorem], <generic-base-change>)
    index-entry([finiteness theorem], qualifier: [for the six functors], <finiteness-of-six-functors>)

    // Section 9.4: Verdier duality
    index-entry([dualizing complex functor], qualifier: [$DD_X$], <defn-dualizing-complex-functor>)
    index-entry([Verdier duality], <verdier-duality>)

    // Section 9.5: The six functor formalism
    index-entry([six functor formalism], <six-functor-formalism>)

    // Appendix A1: Passage to limits
    index-entry([noetherian approximation], qualifier: [absolute], <absolute-noetherian-approx>)
    index-entry([noetherian approximation], qualifier: [relative], <relative-approx>)
    index-entry([passage to limit], qualifier: [for morphisms], <passage-to-limit-of-morphisms>)
    index-entry([passage to limit], qualifier: [for properties of morphisms], <passage-to-limit-of-properties>)
    index-entry([passage to limit], qualifier: [for sheaves], <passage-to-limit-of-sheaves>)

    // Appendix A2: Tsen's theorem
    index-entry([$C_1$ field], <defn-c1-field>)
    index-entry([quasi-algebraically closed field], <defn-c1-field>)
    index-entry([Tsen theorem], <tsen-theorem>)

    // Appendix A3: Beck-Chevalley base change
    index-entry([Beck-Chevalley base change], qualifier: [$BC(f, f', g, g', t)$], <bcbc-defn>)

    // Appendix A4.2: Neron smoothing
    index-entry([affine Neron blowup], qualifier: [$D^+$], <defn-affine-neron-blowup>)
    index-entry([Neron smoothing], <classical-neron-smoothing>)

    // Appendix A4.3: Weierstrass divisibility induction
    index-entry([Artin approximation theorem], <artin-approximation-theorem>)

    // Appendix A5: Strict henselization and quasi-finite maps
    index-entry([strict henselization], qualifier: [along a quasi-finite map], <strict-hs-and-qfinite>)
    index-entry([strict henselization], qualifier: [of a fiber product], <strict-henselizations-tensors-and-qfinites>)

    // Appendix A6: Brown representability
    index-entry([Gabriel-Popescu theorem], <gabriel-popescu>)
    index-entry([compact object], <compact-objects-and-generators>)
    index-entry([generating family], qualifier: [of compact objects], <compact-objects-and-generators>)
    index-entry([telescoping construction], <telescoping-construction>)
    index-entry([Brown representability theorem], <brown-representability>)
  })})
  v(1fr)
})
