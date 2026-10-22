#let compile-cfg = {
  // version number
  // odd minor version number  = beta build
  // even minor version number = release build
  let version = (1, 1, 0)
  // When print-mode is true, all theorem boxes will be white for printing on white paper
  let print-mode = false
  // When html-mode is true, we will #set page(height: auto) and emit one continuous large page
  let html-mode = false
  // When ide-mode is true, we will only compile a few sections
  let ide-mode = "tinymist-vscode" in sys.inputs
  // Embed source code as PDF metadata for distribution
  let distribute-sources = true
  // include a copy of the license
  let license = true
  // include a copy of the cover page image
  let censor-cover-pic = false
  let cover-pic-name = "cover-page-image-v1.0.png"
  let cover-pic-comment = [illustration _Smooth Base Change_ by Irisu]
  let cover-pic-bounds = (height: 40%)
  // include a notice for this file being an internal build
  let internal-build = false

  (
      version: version
    , print-mode: print-mode and not ide-mode
    , html-mode: html-mode and not print-mode and not ide-mode
    , ide-mode: ide-mode
    , distribute-sources: distribute-sources and not ide-mode
    , license: license and not internal-build
    , cover-pic: if (censor-cover-pic) { (censored: true) } else {
      (
        censored: false, 
        name: cover-pic-name, 
        comment: cover-pic-comment, 
        bounds: cover-pic-bounds
      )
    }
    , internal-build: internal-build
  )  
}