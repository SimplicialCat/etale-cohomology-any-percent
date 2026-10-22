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
      // 内部构建提示
      #if (compile-cfg.internal-build) [
        #place(center, dy: 24pt)[#text(size: 20pt, fill: red, weight: "bold")[`内部构建`\ `禁止外传`]]
        #place(bottom + center, dy: -24pt)[#text(size: 20pt, fill: red, weight: "bold")[`内部构建`\ `禁止外传`]]
      ]

      // 标题
      #place(center, dy: 15%)[
        #text(size: 26pt)[平展上同调#text(size: 15pt)[（Any%）]] \ #v(0pt)
      ]
      
      // 封面图
      #place(center, dy: 26%)[
        #if (compile-cfg.cover-pic.censored) {
          align(center, box(width: 37.5% * calc.sqrt(2), height: 50%, stroke: black)[
            #align(center + horizon)[
              `图片占位符`\
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
      
      // 作者、日期
      #place(center, dy: 78%)[
        #text(size: 16pt)[Void 编写]\ #v(0pt)
        #text(size: 12pt)[中文版由 DeepSeek V4.1 Flash 1017 翻译]\ #v(0pt)
        #let today = datetime.today()
        #text(size: 12pt, {
          if (version == none) {
            [未编号构建 ]
            if (hash != none) [\##hash ]
            [编译于 #datetime.today().display("[year]/[month]/[day]")]
          } else if (calc.rem(version.at(1), 2) == 1) {
            // 次版本号为奇数 = 测试版
            // 次版本号为偶数 = 正式版
            // 沿用 GHC 的版本号风格
            [测试版 ]
            for v in version [#v.]
            today.display("[year][month][day]").slice(2) // 截成 6 位日期——7975 年后会失效，不过无所谓
            if (hash != none) [\##hash ]
          } else {
            [正式版 ]
            for (i, v) in version.enumerate() {
              [#v]
              if (i != version.len() - 1) [.]
            }
            [，#datetime.today().display("[year]/[month]/[day]")]
          }
        })
        #if compile-cfg.distribute-sources {
          text(size: 8pt)[
            #set par(spacing: 1em)
            本文档的全部源码与资源均已作为附件包含在此 PDF 中\
            可在命令行使用 `pdfdetach -saveall <file-name>` 提取这些文件，并用 Typst #sys.version 复现本文档\
            `pdfdetach` 可从主流 Linux 发行版的包管理器获取，Windows 上也可另行下载#v(1.5em)

            本文档的源码与发行版也可在以下地址找到：\
            #link("https://github.com/SimplicialCat/etale-cohomology-any-percent", text(fill: blue.darken(25%), raw("https://github.com/SimplicialCat/etale-cohomology-any-percent")))
          ]
        }
      ]
      ]
        
    ]
}
