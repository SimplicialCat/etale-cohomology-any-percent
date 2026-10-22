#import "void-import.typ": *

#let index-entry(name, qualifier: none, loc, sort-key: none) = {
  ((
    name: name, 
    qualifier: qualifier, 
    loc: loc,
    sort-key: sort-key,
  ),)
}
#let make-index(index-entries) = {
  let entries-by-name = (:)
  for entry in index-entries {
    let known-entries = entries-by-name.at(repr(entry.name), default: ())
    known-entries.push((
      name: entry.name, 
      qualifier: entry.qualifier, 
      sort-key: entry.sort-key,
      loc: query(entry.loc).map(it => numbering("1", ..counter(page).at(it.location()))).at(0, default: "-999")
    ))
    entries-by-name.insert(repr(entry.name), known-entries)
  }
  // todo: replace repr() with a more sensible function
  for (_, entries) in entries-by-name.pairs().sorted(key: arr => {
    let (_, es) = arr
    let k = es.at(0).sort-key
    if k == none { repr(es.at(0).name) } else { k }
  }) {
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
  [= 索引]
  columns(2, {context make-index({
    // Section 2.1: Unramified, etale and smooth morphisms
    index-entry([Kähler 微分], qualifier: [$Omega_(X\/Y)$], sort-key: "kahler wei fen", <kahler-differentials>)
    index-entry([非分歧态射], sort-key: "fei fen qi tai she", <defn-unramified-and-etale-morphisms>)
    index-entry([平展态射], sort-key: "ping zhan tai she", <defn-unramified-and-etale-morphisms>)
    index-entry([Kummer 覆盖], sort-key: "kummer fu gai", <kummer-and-artin-schreier-coverings>)
    index-entry([Artin–Schreier 覆盖], sort-key: "artin schreier fu gai", <kummer-and-artin-schreier-coverings>)
    index-entry([Jacobi 判别法], qualifier: [平展性], sort-key: "jacobi pan bie fa", <jacobian-criterion-for-etaleness>)
    index-entry([光滑态射], sort-key: "guang hua tai she", <defn-smooth-morphisms>)

    // Section 2.2: Local structure of etale morphisms
    index-entry([平展态射], qualifier: [标准], sort-key: "ping zhan tai she", <defn-standard-etale-morphism>)

    // Section 2.3: Infinitesimal lifting criterion
    index-entry([形式光滑态射], sort-key: "xing shi guang hua tai she", <defn-formal-morphisms>)
    index-entry([形式非分歧态射], sort-key: "xing shi fei fen qi tai she", <defn-formal-morphisms>)
    index-entry([形式平展态射], sort-key: "xing shi ping zhan tai she", <defn-formal-morphisms>)
    index-entry([无穷小提升判别法], sort-key: "wu qiong xiao ti sheng pan bie fa", <infinitesimal-lifting-criterion>)

    // Section 2.4: Fpqc descent
    index-entry([忠实平坦态射], sort-key: "zhong shi ping tan tai she", <defn-faithfully-flat-and-fpqc-morphisms>)
    index-entry([fpqc 态射], sort-key: "fpqc tai she", <defn-faithfully-flat-and-fpqc-morphisms>)
    // index-entry([base-change notation], qualifier: [$X', X'', X'''$], <descent-notation>)
    // index-entry([Cech nerve notation], qualifier: [$S'', S'''$], <descent-notation>)
    index-entry([典范下降数据], sort-key: "dian fan xia jiang shu ju", <descent-data>)
    index-entry([下降数据], qualifier: [$"DD"(f)$], sort-key: "xia jiang shu ju", <descent-data>)
    index-entry([Amitsur 序列], sort-key: "amitsur xu lie", <amitsur-complex-exact>)

    // Section 2.5: Henselizations & strict henselizations
    index-entry([Hensel 局部环], sort-key: "hensel ju bu huan", <defn-henselian-local-rings>)
    index-entry([严格 Hensel 局部环], sort-key: "yan ge hensel ju bu huan", <defn-henselian-local-rings>)
    index-entry([Hensel 化], qualifier: [$A^#[h]$], sort-key: "hensel hua", <defn-henselizations>)
    index-entry([严格 Hensel 化], qualifier: [$A^#[sh]$], sort-key: "yan ge hensel hua", <defn-henselizations>)

    // Section 2.A1: Radicial morphisms
    index-entry([根性态射], sort-key: "gen xing tai she", <defn-radicial-morphism>)
    index-entry([泛同胚], sort-key: "fan tong pei", <radicial-morphism-first-props>)

    // Section 3.1: Etale covering spaces
    index-entry([平展覆盖], sort-key: "ping zhan fu gai", <terminology-etale-coverings>)
    index-entry([有限平展覆叠空间], qualifier: [$FEt_X$], sort-key: "you xian ping zhan fu die kong jian", <terminology-etale-coverings>)
    index-entry([几何点], sort-key: "ji he dian", <defn-geometric-points>)
    index-entry([带点概形], sort-key: "dai dian gai xing", <defn-geometric-points>)
    index-entry([纤维函子], sort-key: "xian wei han zi", <defn-fiber-functor>)

    // Section 3.2: Galois covering spaces
    index-entry([Galois 覆叠空间], sort-key: "galois fu die kong jian", <defn-galois-covering-space>)
    index-entry([Galois 闭包], sort-key: "galois bi bao", <galois-closure-exists>)
    index-entry([商], qualifier: [有限群], sort-key: "shang", <defn-quotient-by-finite-group>)
    index-entry([容许作用], sort-key: "rong xu zuo yong", <defn-admissible-group-action>)
    index-entry([惯性群], qualifier: [$I_(G)(z)$], sort-key: "guan xing qun", <defn-inertia-group>)

    // Section 3.3: Etale fundamental group
    index-entry([平展基本群], qualifier: [$pi_(1)^(et)(X, ol(x))$], sort-key: "ping zhan ji ben qun", <defn-etale-fundamental-group>)
    index-entry([投射有限群], qualifier: [平展基本群], sort-key: "tou she you xian qun", <pi1et-as-invlim>)

    // Section 4.1: Sites
    index-entry([景], sort-key: "jing", <defn-site>)
    index-entry([预层], sort-key: "yu ceng", <defn-presheaves-and-sheaves-on-sites>)
    index-entry([层], sort-key: "ceng", <defn-presheaves-and-sheaves-on-sites>)
    index-entry([平展景], qualifier: [$X_"et"$], sort-key: "ping zhan jing", <defn-etale-site>)
    index-entry([平展层], sort-key: "ping zhan ceng", <defn-etale-site>)

    // Section 4.3: Sheaf cohomology
    index-entry([Čech 上同调], qualifier: [零次], sort-key: "cech shang tong diao", <constr-zeroth-cech-cohom>)
    index-entry([层化], qualifier: [$(-)^\#$], sort-key: "ceng hua", <defn-sheafification>)
    index-entry([常值层], qualifier: [$ul(M)_X$], sort-key: "chang zhi ceng", <detection-and-const-sheaf>)
    index-entry([平展上同调], qualifier: [$H^(bullet)_(et)(X, -)$], sort-key: "ping zhan shang tong diao", <defn-etale-cohomology>)

    // Section 4.4: Derived functors
    index-entry([直接像], qualifier: [$f_*$], sort-key: "zhi jie xiang", <defn-etale-direct-image>)
    index-entry([逆像], qualifier: [$f^(-1)$], sort-key: "ni xiang", <defn-etale-sheaf-inverse-image>)
    index-entry([高阶直接像], qualifier: [$R^q f_*$], sort-key: "gao jie zhi jie xiang", <defn-higher-direct-image>)
    index-entry([谱序列], qualifier: [Leray], sort-key: "pu xu lie", <derived-lower-star-first-props>)

    // Section 4.5: Stalks
    index-entry([茎], sort-key: "jing", <defn-etale-stalk>)
    index-entry([芽], sort-key: "ya", <defn-germs-and-support>)
    index-entry([支集], sort-key: "zhi ji", <defn-germs-and-support>)
    index-entry([Godement 消解], sort-key: "godement xiao jie", <injective-godement-resolution>)

    // Section 4.6: Cech cohomology
    index-entry([Čech 上同调], sort-key: "cech shang tong diao", <constr-cech-cohom>)
    index-entry([谱序列], qualifier: [Čech 到导出函子], sort-key: "pu xu lie", <cech-to-derived-functor-spectral-sequence>)

    // Section 4.7: Open and closed immersions
    index-entry([零延拓], qualifier: [$f_!$], sort-key: "ling yan tuo", <etale-lower-shriek-defn>)
    index-entry([例外逆像], qualifier: [$i^!$], sort-key: "li wai ni xiang", <closed-immersion-upper-shriek-constr>)

    // Section 4.8: Torsion sheaves
    index-entry([挠层], sort-key: "nao ceng", <defn-torsion-sheaf>)
    index-entry([$ZZ\/n$-模层], sort-key: "0mo ceng", <defn-zn-module-sheaf>)

    // Section 4.9: Internal Hom and tensor
    index-entry([平展环层], sort-key: "ping zhan huan ceng", <defn-etale-ring-and-module-sheaves>)
    index-entry([平展模层], sort-key: "ping zhan mo ceng", <defn-etale-ring-and-module-sheaves>)
    index-entry([内 Hom], sort-key: "nei hom", <defn-internal-hom>)
    index-entry([张量积], qualifier: [平展层], sort-key: "zhang liang ji", <defn-sheaf-tensor-product>)

    // Section 4.A1: Derived category statements
    index-entry([上同调维数], sort-key: "shang tong diao wei shu", <defn-cohomological-dimension>)
    index-entry([导出范畴], qualifier: [平展层], sort-key: "dao chu fan chou", <derived-categories-of-etale-sheaves>)
    index-entry([导出范畴], qualifier: [挠平展层], sort-key: "dao chu fan chou", <derived-categories-of-etale-sheaves>)

    // Section 5.1: Limit formulas
    index-entry([极限公式], qualifier: [层], sort-key: "ji xian gong shi", <limit-formula-for-sheaves>)
    index-entry([极限公式], qualifier: [概形], sort-key: "ji xian gong shi", <limit-formula-for-schemes>)
    index-entry([严格局部化], qualifier: [$cal(O)_(X, ol(x))$], sort-key: "yan ge ju bu hua", <strict-local-ring-and-localization>)
    index-entry([严格局部化], qualifier: [$tilde(X)_(ol(x))$], sort-key: "yan ge ju bu hua", <strict-local-ring-and-localization>)
    index-entry([茎], qualifier: [导出直接像], sort-key: "jing", <stalks-of-derived-lowerstar>)

    // Section 5.2: Etale cohomology of quasi-coherent sheaves
    index-entry([平展上同调], qualifier: [拟凝聚层], sort-key: "ping zhan shang tong diao", <etale-cohom-of-qcoh-sheaf>)

    // Section 5.3: H1 of the multiplicative group
    index-entry([乘法群], qualifier: [$H^(1)_(et)(X, GG_m) = "Pic"(X)$], sort-key: "cheng fa qun", <h1-of-gm-is-pic>)

    // Section 5.4: H1 of a constant sheaf
    index-entry([平展主丛], sort-key: "ping zhan zhu cong", <defn-etale-g-torsor>)
    index-entry([平展主丛], qualifier: [带基点], sort-key: "ping zhan zhu cong", <defn-etale-g-torsor>)
    index-entry([主丛分类], qualifier: [平展基本群], sort-key: "zhu cong fen lei", <hom-from-pi1-classifies-torsors>)
    index-entry([主丛分类], qualifier: [由 $caron(H)^1$], sort-key: "zhu cong fen lei", <cech-h1-classifies-torsors>)

    // Section 5.5: Topological invariance
    index-entry([拓扑不变性], sort-key: "tuo pu bu bian xing", <top-invariance>)

    // Section 5.6: The etale site of a field
    index-entry([平展景], qualifier: [域], sort-key: "ping zhan jing", <struct-of-spec-k-et>)
    index-entry([Galois 上同调], sort-key: "galois shang tong diao", <galois-cohom-props>)

    // Section 5.7: Etale cohomology of curves
    index-entry([除子正合列], sort-key: "chu zi zheng he lie", <divisor-exact-sequence>)
    index-entry([平展上同调], qualifier: [曲线], sort-key: "ping zhan shang tong diao", <cohom-of-general-curve>)

    // Section 6.1: Proper base change setup
    index-entry([基变换态射], qualifier: [$g^(-1) R^q f_* -> R^q f'_* g'^(-1)$], sort-key: "ji bian huan tai she", <base-change-constr>)
    index-entry([紧合基变换定理], sort-key: "jin he ji bian huan ding li", <proper-base-change>)

    // Section 6.2: Constructible sheaves
    index-entry([局部常值层], sort-key: "ju bu chang zhi ceng", <defn-locally-constant-and-lcc-sheaves>)
    index-entry([局部常值可构造层], qualifier: [l.c.c. 层], sort-key: "ju bu chang zhi ke gou zao ceng", <defn-locally-constant-and-lcc-sheaves>)
    index-entry([泛化], qualifier: [几何点], sort-key: "fan hua", <defn-specialization-morphism>)
    index-entry([特殊化态射], qualifier: [$sp_(ol(x), ol(eta))$], sort-key: "te shu hua tai she", <defn-specialization-morphism>)
    index-entry([可表示平展层], qualifier: [$h_Y$], sort-key: "ke biao shi ping zhan ceng", <representable-etale-sheaf>)
    index-entry([可构造层], sort-key: "ke gou zao ceng", <defn-constructible-sheaf>)
    index-entry([导出范畴], qualifier: [可构造平展层], sort-key: "dao chu fan chou", <constructible-derived-categories>)

    // Section 6.7: Proof of Seed
    index-entry([Grothendieck 存在性定理], sort-key: "grothendieck cun zai xing ding li", <grothendieck-existence-thm>)

    // Section 6.8: Higher vanishing
    index-entry([平展上同调维数], qualifier: [$cd(X)$], sort-key: "ping zhan shang tong diao wei shu", <etale-cohomological-dimension>)
    index-entry([消没定理], qualifier: [Artin], sort-key: "xiao mo ding li", <artin-vanishing>)
    index-entry([消没定理], qualifier: [Grothendieck], sort-key: "xiao mo ding li", <grothendieck-vanishing>)
    index-entry([消没定理], qualifier: [相对 Artin], sort-key: "xiao mo ding li", <relative-artin-grothendieck-vanishing>)
    index-entry([消没定理], qualifier: [相对 Grothendieck], sort-key: "xiao mo ding li", <relative-artin-grothendieck-vanishing>)

    // Section 6.A1: Derived category statements
    index-entry([紧合基变换定理], qualifier: [导出], sort-key: "jin he ji bian huan ding li", <derived-base-changes>)

    // Section 7.1: Construction of Rf! and compactly supported cohomology
    index-entry([Nagata 紧化], sort-key: "nagata jin hua", <nagata-compactification>)
    index-entry([紧化], qualifier: [态射], sort-key: "jin hua", <defn-compactification>)
    index-entry([紧支导出推前], qualifier: [$R f_!$], sort-key: "jin zhi dao chu tui qian", <defn-derived-pushforward-with-proper-support>)
    index-entry([紧支上同调], qualifier: [$R Gamma_(c)(X, -)$], sort-key: "jin zhi shang tong diao", <defn-cohomology-with-proper-support>)
    index-entry([紧支高阶直接像], qualifier: [$R^q f_!$], sort-key: "jin zhi gao jie zhi jie xiang", <proper-support-cohomology-notation>)
    index-entry([紧支上同调], qualifier: [$H^(q)_(c)(X, -)$], sort-key: "jin zhi shang tong diao", <proper-support-cohomology-notation>)

    // Section 7.3: Projection and Kunneth formulas
    index-entry([投影公式], sort-key: "tou ying gong shi", <projection-formula>)
    index-entry([Künneth 公式], sort-key: "kunneth gong shi", <kunneth-formula>)

    // Section 8.1: General reduction on base changes
    index-entry([导出范畴], qualifier: [$D^(b)_(#[ctf])(X_et, Lambda)$], sort-key: "dao chu fan chou", <constructible-finite-tor-derived-category>)
    index-entry([相对基变换态射], sort-key: "xiang dui ji bian huan tai she", <relative-base-change-constr>)

    // Section 8.2: Local acyclicity
    index-entry([消没圈簇], qualifier: [$F_(ol(x), ol(t))$], sort-key: "xiao mo quan cu", <defn-local-acyclicity>)
    index-entry([局部零调性], sort-key: "ju bu ling diao xing", <defn-local-acyclicity>)
    index-entry([泛局部零调性], sort-key: "fan ju bu ling diao xing", <defn-local-acyclicity>)
    index-entry([余特殊化映射], qualifier: [$"cosp"$], sort-key: "yu te shu hua ying she", <cospecialization-map>)

    // Section 8.3: Smooth base change
    index-entry([光滑基变换定理], sort-key: "guang hua ji bian huan ding li", <smooth-base-change>)

    // Section 8.4: Finiteness of Rf!
    index-entry([有限性定理], qualifier: [紧支导出推前], sort-key: "you xian xing ding li", <finiteness-of-lower-shriek>)

    // Section 9.1: Trace map of a smooth morphism
    index-entry([迹映射], qualifier: [$Tr_(X\/Y)$], sort-key: "ji ying she", <existence-of-trace-map>)
    index-entry([Tate 扭], qualifier: [$cal(K)(m)$], sort-key: "tate niu", <defn-tate-twists>)

    // Section 9.2: Poincare duality
    index-entry([杯积配对], qualifier: [$smile$], sort-key: "bei ji pei dui", <defn-cup-product-pairing>)
    index-entry([例外逆像], qualifier: [$R f^!$], sort-key: "li wai ni xiang", <existence-of-upper-shriek>)
    index-entry([纯度映射], qualifier: [$t_(X\/Y)$], sort-key: "chun du ying she", <purity-map>)
    index-entry([Poincaré 对偶], qualifier: [相对], sort-key: "poincare dui ou", <relative-poincare-duality>)
    index-entry([Poincaré 对偶], qualifier: [绝对], sort-key: "poincare dui ou", <absolute-poincare-duality>)
    index-entry([纯度], qualifier: [相对], sort-key: "chun du", <relative-purity>)

    // Section 9.3: Generic base change and finiteness
    index-entry([泛基变换定理], sort-key: "fan ji bian huan ding li", <generic-base-change>)
    index-entry([有限性定理], qualifier: [六函子], sort-key: "you xian xing ding li", <finiteness-of-six-functors>)

    // Section 9.4: Verdier duality
    index-entry([对偶复形函子], qualifier: [$DD_X$], sort-key: "dui ou fu xing han zi", <defn-dualizing-complex-functor>)
    index-entry([Verdier 对偶], sort-key: "verdier dui ou", <verdier-duality>)

    // Section 9.5: The six functor formalism
    index-entry([六函子形式], sort-key: "liu han zi xing shi", <six-functor-formalism>)

    // Appendix A1: Passage to limits
    index-entry([Noether 逼近], qualifier: [绝对], sort-key: "noether bi jin", <absolute-noetherian-approx>)
    index-entry([Noether 逼近], qualifier: [相对], sort-key: "noether bi jin", <relative-approx>)
    index-entry([极限论证], qualifier: [态射], sort-key: "ji xian lun zheng", <passage-to-limit-of-morphisms>)
    index-entry([极限论证], qualifier: [态射的性质], sort-key: "ji xian lun zheng", <passage-to-limit-of-properties>)
    index-entry([极限论证], qualifier: [层], sort-key: "ji xian lun zheng", <passage-to-limit-of-sheaves>)

    // Appendix A2: Tsen's theorem
    index-entry([$C_1$ 域], sort-key: "0c1 yu", <defn-c1-field>)
    index-entry([拟代数闭域], sort-key: "ni dai shu bi yu", <defn-c1-field>)
    index-entry([曾炯定理], sort-key: "zeng jiong ding li", <tsen-theorem>)

    // Appendix A3: Beck-Chevalley base change
    index-entry([Beck–Chevalley 基变换], qualifier: [$BC(f, f', g, g', t)$], sort-key: "beck chevalley ji bian huan", <bcbc-defn>)

    // Appendix A4.2: Neron smoothing
    index-entry([仿射 Néron 爆破], qualifier: [$D^+$], sort-key: "fang she neron bao po", <defn-affine-neron-blowup>)
    index-entry([Néron 光滑化], sort-key: "neron guang hua", <classical-neron-smoothing>)

    // Appendix A4.3: Weierstrass divisibility induction
    index-entry([Artin 逼近定理], sort-key: "artin bi jin ding li", <artin-approximation-theorem>)

    // Appendix A5: Strict henselization and quasi-finite maps
    index-entry([严格 Hensel 化], qualifier: [沿拟有限映射], sort-key: "yan ge hensel hua", <strict-hs-and-qfinite>)
    index-entry([严格 Hensel 化], qualifier: [纤维积], sort-key: "yan ge hensel hua", <strict-henselizations-tensors-and-qfinites>)

    // Appendix A6: Brown representability
    index-entry([Gabriel–Popescu 定理], sort-key: "gabriel popescu ding li", <gabriel-popescu>)
    index-entry([紧对象], sort-key: "jin dui xiang", <compact-objects-and-generators>)
    index-entry([生成族], qualifier: [紧对象], sort-key: "sheng cheng zu", <compact-objects-and-generators>)
    index-entry([望远镜构造], sort-key: "wang yuan jing gou zao", <telescoping-construction>)
    index-entry([Brown 可表示性定理], sort-key: "brown ke biao shi xing ding li", <brown-representability>)
  })})
  v(1fr)
})
