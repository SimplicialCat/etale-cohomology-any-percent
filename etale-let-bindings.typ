#import "@preview/commute:0.3.0" as commute
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/ouset:0.2.0": *
#import "void-rubby.typ": *

#let invlim = math.op(underset([lim], [#scale(math.arrow.l.long, x: 160%)]), limits: true)
#let dirlim = math.op(underset([lim], [#scale(math.arrow.r.long, x: 160%)]), limits: true)
#let dircolim = math.op(underset([colim], [#scale(math.arrow.r.long, x: 160%)]), limits: true)

// #let cite-stacks(tag, index) = {
//   [#link("https://stacks.math.columbia.edu/tag/" + tag, [#raw(tag) / #index of Stacks Project])]
// }
#let cite-stacks(tag, index) = {
  cite(<cite-SP>, supplement: link("https://stacks.math.columbia.edu/tag/" + tag, text(fill: blue.darken(25%), raw(tag) + [ \/ ] + index)))
}

// https://forum.typst.app/t/how-does-one-avoid-caligraphic-font-difference-between-typst-and-latex/1781/5
// Workaround to get LaTeX-like \mathcal in Typst
#let cal(it) = math.class("normal", context {
  show math.equation: set text(font: "Garamond-Math", stylistic-set: 3)

  let scaling = 100% * (1em.to-absolute() / text.size)
  let wrapper = if scaling < 60% { math.sscript }
                else if scaling < 100% { math.script }
                else { it => it }
  
  box(text(top-edge: "bounds", $wrapper(math.cal(it))$))
})

#let ab = math.op[ab]
#let BC = math.op[BC]
#let Cl = math.op[Cl]
#let cd = math.op[cd]
#let et = math.op[et]
#let Et = math.bold[Et]
#let GL = math.op[GL]
#let Im = math.op[Im]
#let Nm = math.op[Nm]
#let Re = math.op[Re]
#let sp = math.op[sp]
#let Tr = math.op[Tr]
#let wp = math.op("\u{2118}")
#let Alt = $scripts(and.big)$
#let Aut = math.op[Aut]
#let cAb = math.bold[Ab]
#let cSh = math.bold[Sh]
#let Coh = math.bold[Coh]
#let Div = math.op[Div]
#let End = math.op[End]
#let Ext = math.op[Ext]
#let FEt = math.bold[FEt]
#let Gal = math.op[Gal]
#let Hom = math.op[Hom]
#let Ind = math.op[Ind]
#let opp = math.op[op]
#let Pic = math.op[Pic]
#let rad = math.op[rad]
#let res = math.op[res]
#let sep = math.op[sep]
#let Sym = math.op[Sym]
#let trd = math.op[trd]
#let cart = math.op("\u{231c}")
#let AAlg(A) = $#A#[-]bold(#[Alg])$
#let CaCl = math.op[CaCl]
#let cGrp = math.bold[Grp]
#let cong = math.tilde.equiv
#let cosp = math.op[cosp]
#let cPAb = math.bold[PAb]
#let cPSh = math.bold[PSh]
#let cSch = math.bold[Sch]
#let cSet = math.bold[Set]
#let EExt = math.op[$cal(E)$#h(-1.2pt)xt]
#let Frac = math.op[Frac]
#let GSet(G) = $#G#[-]bold(#[Set])$
#let HHom = math.op[$cal(H)$#h(-0.8pt)om]
#let Idem = math.op[Idem]
#let Proj = math.op[Proj]
#let QCoh = math.bold[QCoh]
#let RHom = math.op[$R$Hom]
#let Spec = math.op[Spec]
#let SPec = math.op(math.bold[Spec])
#let supp = math.op[supp]
#let CaDiv = math.op[CaDiv]
#let coker = math.op[coker]
#let coInd = math.op[coInd]
#let colim = math.op(limits: true)[colim]
#let oplus = math.plus.o
#let RHHom = math.op[$R$$cal(H)$#h(-0.8pt)om]
#let length = math.op[length]
#let otimes = math.times.o
#let Lotimes = math.op(limits: false, overset($times.o$, $L$))

#let ol(..x) = math.overline(..x)
#let ul(..x) = math.underline(..x)
#let fps(x) = $[#h(-0.15em) [#x] #h(-0.15em)]$
#let AMod(x) = [$bold("Mod")(#x)$]

#let gen(..args) = $lr(chevron.l #{
  args = args.pos()
  args.remove(0)
  for x in args {$,#x$}
} chevron.r)$

// nullify the width of an alignment column in math mode
#let killcol = h(-1000000pt)

#let ignore-todo = true
// to see todos in document, set ignore-todo = false
// then every #todo will throw an error
#let todo(soft: false) = [#text("todo", weight: "bold", fill: if (soft) {blue} else {red})#assert(ignore-todo or soft, message: "todo")]
#let soft-todo() = todo(soft: true)

#let qed-symb = $square$
#let insert-qed = [#h(1fr)#qed-symb]

#let snap-width(body, factor: 100%) = layout(size => context {
  let width = size.width * factor
  let old-width = measure(body).width
  let factor = (width / old-width) * 100%
  scale(reflow: true, x: factor, y: factor, body)
})

// tune the coordinates of a 2-morphism in a commutative diagram
#let tune-2-mor-coords(p1, p2, l: 0.42) = {
  let (x1, y1) = p1
  let (x2, y2) = p2
  let (dx, dy) = (x2 - x1, y2 - y1)
  let r = calc.sqrt(dx * dx + dy * dy)
  let (fx, fy) = (dx / r, dy / r)
  return ((x1 + l * fx, y1 + l * fy), (x2 - l * fx, y2 - l * fy))
}
#let lerp-point(p1, p2, a: 0) = {
  return p1.zip(p2).map(arr => (1 - a) * arr.at(0) + a * arr.at(1))
}
#let midpoint = lerp-point.with(a: 0.5)