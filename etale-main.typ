#import "void-import.typ": *
#import "etale-nonmath.typ" as nonmath

#show: void-style

#let all-sections = (
  (1, (0,), <chapter-intro>),
  (2, (1, "A1", 2, 3, 4, 5), <chapter-etale-morphism>), 
  (3, (1, 2, 3, 4), <chapter-etale-pi1>),
  (4, (1, 2, 3, 4, 5, 6, 7, 8, 9, "A1"), <chapter-etale-sheaves>), 
  (5, (1, 2, 3, 4, 5, 6, 7), <chapter-etale-cohom>), 
  (6, (1, 2, 3, 4, 5, 6, 7, 8, "A1"), <chapter-pbc>), 
  (7, (1, 2, 3), <chapter-lower-shriek>),
  (8, (1, 2, 3, 4), <chapter-local-acyc>),
  (9, (1, 2, 3, 4, 5), <chapter-poincare-duality>), 
  ("A1", (0,), <appendix-passage-to-limit>), 
  ("A2", (0,), <appendix-tsen-thm>), 
  ("A3", (0,), <appendix-bcbc>), 
  ("A4", (1, 2, 3), <appendix-artin-approximation>), 
  ("A5", (0,), <appendix-strict-hs-and-qfinites>), 
  ("A6", (0,), <appendix-brown-representability>)
)
#let chap-titles = (
  c1: "Introduction",
  c2: "Etale morphisms",
  c3: "Etale fundamental group",
  c4: "Etale site",
  c5: "Basics of etale cohomology",
  c6: "Proper base change", 
  c7: "Pushforward with proper support",
  c8: "Local acyclicity", 
  c9: "Poincare duality", 
  cA1: "Passage to limit",
  cA2: "Tsen's theorem", 
  cA3: "Beck-Chevalley base change", 
  cA4: "Artin approximation", 
  cA5: "Strict henselization and quasi-finite maps", 
  cA6: "Brown representability"
)
#let active-sections = if (compile-cfg.ide-mode) {
  all-sections.filter(chap => (chap.at(0) in (5,)) or (false and type(chap.at(0)) == str and "A" in chap.at(0)))
} else {all-sections}

#let doc-body = for (chap-name, chap-arr, chap-lab) in active-sections {
  let chap-index = void-style-parse-heading-name(chap-name)
  counter(heading).update((..arr) => (chap-index - 1, ))
  [#heading(text(chap-titles.at("c" + str(chap-name))))#chap-lab]
  for sect-name in chap-arr {
    let sect-index = void-style-parse-heading-name(sect-name)
    if (sect-index >= 1) {
      counter(heading).update((..arr) => (arr.at(0), sect-index - 1))
    }
    let file-name = "etale-c" + str(chap-name) + "s" + str(sect-name) + ".typ"
    include file-name
  }
}

#let other-sources = {
  (
    "void-config", "void-crc32", "void-import", "etale-let-bindings", "void-staged-cd-helpers", "void-rubby", "void-style", "void-theorem", "cover-page", "etale-main", "symbol-index", "etale-nonmath", "references.bib", "void-custom-cite.csl", "README.md"
  )
  if (not compile-cfg.cover-pic.censored) {
    (compile-cfg.cover-pic.name,)
  }
  if (compile-cfg.license) {
    ("license", "LICENSE..")
  }
}

#if compile-cfg.distribute-sources {
  // Attach all source files to the PDF
  let attached-sources = for (chap-num, chap-arr, _) in active-sections {
    for sect-num in chap-arr {
      let file-name = "etale-c" + str(chap-num) + "s" + str(sect-num) + ".typ"
      pdf.attach(
        file-name, 
        relationship: "source", 
        mime-type: "text/vnd.typst", 
        description: "Source file " + file-name + " for this document."
      )
    }
  } + for other-source in other-sources {
    let file-name = if not "." in other-source { other-source + ".typ" } else if other-source.ends-with("..") { other-source.slice(0, -2) } else { other-source }
    pdf.attach(
      file-name,
      relationship: "source",
      mime-type: if file-name.ends-with(".typ") { "text/vnd.typst" /* otherwise unknown */},
      description: "Misc source file " + file-name + " for this document.",
    )
  }
  attached-sources
}

#import "cover-page.typ": cover-page
#cover-page(version: compile-cfg.version, hash: if compile-cfg.ide-mode {none} else {
  let doc-source = for (chap-num, chap-arr, _) in active-sections {
    for sect-num in chap-arr {
      let file-name = "etale-c" + str(chap-num) + "s" + str(sect-num) + ".typ"
      bytes(file-name)
      bytes("{{{")
      bytes(read(file-name, encoding: none))
      bytes("}}}")
    }
  } + for other-source in other-sources {
    let file-name = if not "." in other-source { other-source + ".typ" } else if other-source.ends-with("..") { other-source.slice(0, -2) } else { other-source }
    bytes(file-name)
    bytes("{{{")
    bytes(read(file-name, encoding: none))
    bytes("}}}")
  }
  let doc-hash = hash-crc32-hex-str(doc-source)
  doc-hash})
#if (compile-cfg.license) { include "license.typ" }
#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9004)
  [= Acknowledgements]
  nonmath.acknowledgements
  v(1fr)
  colbreak()
  counter(heading).update(9005)
  [= Disclosure of AI usage]
  nonmath.disclosure-of-ai-usage
  v(1fr)
})
#[] <outline-start>
#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9002)
  [= Table of contents]
  outline(depth: 2, target: selector(heading).before(<outline-start>).or(selector(heading).after(<outline-end>)), title: none)
  v(1fr)
})
#[] <outline-end>
#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9006)
  [= Preface]
  nonmath.preface
  v(1fr)
})

#doc-body

#include "symbol-index.typ"

#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9007)
  [= Epilogue]
  nonmath.epilogue
  v(1fr)
})
#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9003)
  bibliography("references.bib", style: "void-custom-cite.csl")
  v(1fr)
})