#import "void-import.typ": *
#let cover-page(version: none, hash: none) = {
  if compile-cfg.ide-mode {
    hash = none
  }
  let box-fn = if compile-cfg.html-mode {
    it => context {
      let page-width = page.width - page.margin.left - page.margin.right
      let simulated-page-height = calc.sqrt(2) * page-width
      box(width: page-width, height: simulated-page-height, stroke: black)[#it]
    }
  } else {
    it => box(width: 100%, height: 100%, stroke: black)[#it]
  }
  box-fn[
    #align(horizon + center)[
      // internal build notice
      #if (compile-cfg.internal-build) [
        #place(center, dy: 24pt)[#text(size: 20pt, fill: red, weight: "bold")[`internal build`\ `unauthorized distribution prohibited`]]
        #place(bottom + center, dy: -24pt)[#text(size: 20pt, fill: red, weight: "bold")[`internal build`\ `unauthorized distribution prohibited`]]
      ]

      // title
      #place(center, dy: 15%)[
        #text(size: 26pt)[Etale Cohomology#text(size: 15pt)[ (Any%)]] \ #v(0pt)
        #text(size: 14pt)[a crash course for the reluctant geometer]
      ]
      
      // cover image
      #place(center, dy: 26%)[
        #if (compile-cfg.cover-pic.censored) {
          align(center, box(width: 37.5% * calc.sqrt(2), height: 50%, stroke: black)[
            #align(center + horizon)[
              `image placeholder`\
              #box(width: 160pt, height: 160pt, stroke: red)[
                #place(dx: 0pt, dy: 0pt, circle(radius: 80pt))
                #place(dx: 30pt, dy: 50pt, circle(radius: 10pt))
                #place(dx: 110pt, dy: 50pt, circle(radius: 10pt))
                #place(curve(
                  curve.move((40pt, 110pt)),
                  curve.quad((80pt, 150pt), (120pt, 110pt)),
                ))
              ]
            ]
          ])
        } else {
          image(..(compile-cfg.cover-pic.bounds), compile-cfg.cover-pic.name)
          if (compile-cfg.cover-pic.comment != none) [
            #text(size: 8pt, compile-cfg.cover-pic.comment) \
          ]
        }
      ]
      
      // author, date
      #place(center, dy: 78%)[
        #text(size: 16pt)[compiled by Void]\ #v(0pt)
        #let today = datetime.today()
        #text(size: 12pt, {
          if (version == none) {
            [unversioned build ]
            if (hash != none) [\##hash ]
            [compiled on #datetime.today().display("[year]/[month]/[day]")]
          } else if (calc.rem(version.at(1), 2) == 1) {
            // Odd minor version = beta build
            // Even minor version = release build
            // This follows GHC's versioning style
            [beta build ]
            for v in version [#v.]
            today.display("[year][month][day]").slice(2) // truncate to 6 digit date - this fails in 7975 years but whatever
            if (hash != none) [\##hash ]
          } else {
            [release build ]
            for (i, v) in version.enumerate() {
              [#v]
              if (i != version.len() - 1) [.]
            }
            [ on #datetime.today().display("[year]/[month]/[day]")]
          }
        })
        #if compile-cfg.distribute-sources {
          text(size: 8pt)[
            #set par(spacing: 1em)
            All source code and resources of this document has been included in this PDF file as attachments\
            You can use `pdfdetach -saveall <file-name>` on command line to extract them and reproduce this document with Typst #sys.version\
            `pdfdetach` is available from package managers on mainstream Linux distros, and may be downloaded separately on Windows#v(1.5em)

            Source and releases of this document may also be found at:\
            #link("https://github.com/SimplicialCat/etale-cohomology-any-percent", text(fill: blue.darken(25%), raw("https://github.com/SimplicialCat/etale-cohomology-any-percent")))
          ]
        }
      ]
      ]
        
    ]
}
