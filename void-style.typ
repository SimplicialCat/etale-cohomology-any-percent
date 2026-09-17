#let void-style-parse-heading-name(s) = {
  if (type(s) == int) {
    return s
  }
  let m = none
  if ({m = s.match(regex("A(\d+)")); m} != none) {
    let n = m.captures.at(0)
    return int(n) + 1000
  }
}

#let void-style-name-heading(n) = {
  if (n < 1000) {
    return str(n)
  } else if (n <= 2000) {
    return "A" + str(n - 1000) // Appendix
  }
}

#let void-style-heading-prefix(lvl, numbers) = {
  if (lvl == 1) {
    if (numbers.at(0) < 1000) { return "Chapter" }
    if (numbers.at(0) <= 2000) { return "Appendix" }
  } else if (lvl == 2) {
    return "Section"
  }
  panic()
}

#let void-style-heading-numbering(..args, last-dot: true) = {
  args = args.pos()
  for (i, n) in args.enumerate() {
    let name = void-style-name-heading(n)
    name
    if ((last-dot or i != args.len() - 1) and args.at(0) <= 9000) { "." }
  }
}

#let void-style(affect-headings: true, it) = [
  #import "void-config.typ": compile-cfg
  #import "etale-let-bindings.typ": qed-symb
  /*
   * Show styles
   */
  #set text(
    font: ((name: "New Computer Modern", covers: "latin-in-cjk"), "FandolSong"),
  )
  #show smartquote: set text(font: "New Computer Modern")
  #set page(
    paper: "a4",
    margin: (x: 30pt, y: 60pt),
    ..if compile-cfg.html-mode {(
      // HTML exclusive settings
      height: auto,
    )} else {(
      // PDF exclusive settings
      footer: context align(center)[#counter(page).get().at(0)],
    )}
  )
  // #set par(justify: true)
  #set heading(
    numbering: void-style-heading-numbering,
    supplement: []
  )
  #let vstyle-first-section = state("vstyle-first-section", false)
  #show heading.where(level: 1): it => {
    set text(size: 18pt, weight: "semibold")
    set align(center)
    context {
      let n = counter(heading).get()
      if (n.at(0) <= 9000) {
        colbreak()
        let prefix = void-style-heading-prefix(1, n)
        let number-str = void-style-heading-numbering(..counter(heading).get())
        [#prefix #it.supplement#number-str #it.body]
      } else {
        [#it.body]
      }
    }
    vstyle-first-section.update(true)
  }
  #show heading.where(level: 2): it => {
    context if not vstyle-first-section.get() { colbreak() }
    set text(size: 15pt, weight: "semibold")
    set align(center)
    context {
      let prefix = void-style-heading-prefix(2, counter(heading).get())
      let number-str = void-style-heading-numbering(..counter(heading).get())
      [#prefix #it.supplement#number-str #it.body]
    }
    vstyle-first-section.update(false)
  }
  #set math.mat(delim: "[")
  #set enum(
    numbering: "(1a)"
  )
  #set math.cases(
    gap: 0% + 0.6em
  )
  #show ref: it => {
    if (it.element == none and (it.citation == none or not str(it.citation.key).starts-with("cite-"))) {
      text(weight: "bold", fill: red)[?? Missing ref ??]
    } else if (it.element != none and it.element.func() == heading and it.element.level <= 2) {
      let elem = it.element
      let lvl = elem.level
      let heading-num = counter(heading).at(elem.location())
      let prefix = void-style-heading-prefix(lvl, heading-num)
      context link(it.target)[#prefix #((heading.numbering)(..heading-num)).slice(0, -1)]
    } else if (it.citation != none) {
      it.citation
    } else {
      it
    }
  }
  #import "@preview/ctheorems:1.1.3" as C
  #show: C.thmrules.with(qed-symbol: qed-symb)

  #it
]