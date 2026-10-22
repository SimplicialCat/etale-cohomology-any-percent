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
  c1: "引言",
  c2: "平展态射",
  c3: "平展基本群",
  c4: "平展景",
  c5: "平展上同调初步",
  c6: "紧合基变换", 
  c7: "紧支推前",
  c8: "局部零调性", 
  c9: "Poincaré 对偶", 
  cA1: "极限论证",
  cA2: "曾炯定理", 
  cA3: "Beck–Chevalley 基变换", 
  cA4: "Artin 逼近", 
  cA5: "严格 Hensel 化与拟有限映射", 
  cA6: "Brown 可表示性"
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
  // 把全部源文件附到 PDF 中
  let attached-sources = for (chap-num, chap-arr, _) in active-sections {
    for sect-num in chap-arr {
      let file-name = "etale-c" + str(chap-num) + "s" + str(sect-num) + ".typ"
      pdf.attach(
        file-name, 
        relationship: "source", 
        mime-type: "text/vnd.typst", 
        description: "本文档的源文件 " + file-name + "。"
      )
    }
  } + for other-source in other-sources {
    let file-name = if not "." in other-source { other-source + ".typ" } else if other-source.ends-with("..") { other-source.slice(0, -2) } else { other-source }
    pdf.attach(
      file-name,
      relationship: "source",
      mime-type: if file-name.ends-with(".typ") { "text/vnd.typst" /* 其他情况未知 */},
      description: "本文档的附属源文件 " + file-name + "。",
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
  [= 致谢]
  nonmath.acknowledgements
  v(1fr)
  colbreak()
  counter(heading).update(9005)
  [= AI 使用说明]
  nonmath.disclosure-of-ai-usage
  v(1fr)
})
#[] <outline-start>
#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9002)
  [= 目录]
  outline(depth: 2, target: selector(heading).before(<outline-start>).or(selector(heading).after(<outline-end>)), title: none)
  v(1fr)
})
#[] <outline-end>
#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9006)
  [= 前言]
  nonmath.preface
  v(1fr)
})

#doc-body

#include "symbol-index.typ"

#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9007)
  [= 后记]
  nonmath.epilogue
  v(1fr)
})
#block(width: 100%, height: auto, inset: (x: 30pt, y: 60pt), stroke: black, breakable: true, {
  counter(heading).update(9003)
  bibliography("references.bib", style: "void-custom-cite.csl")
  v(1fr)
})