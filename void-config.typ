#let compile-cfg = {
  // 版本号
  // 次版本号为奇数 = 测试版
  // 次版本号为偶数 = 正式版
  let version = (1, 1, 0)
  // print-mode 为真时，所有定理框都改为白色，便于在白纸上打印
  let print-mode = false
  // html-mode 为真时，把页面设为自动高度，输出一整页连续内容
  let html-mode = false
  // ide-mode 为真时，只编译少数几节
  let ide-mode = "tinymist-vscode" in sys.inputs
  // 把源码嵌入 PDF 元数据以便分发
  let distribute-sources = true
  // 附上一份许可证副本
  let license = true
  // 附上封面图
  let censor-cover-pic = false
  let cover-pic-name = "cover-page-image-v1.0.png"
  let cover-pic-comment = [《光滑基变换》，Irisu 绘]
  let cover-pic-bounds = (height: 40%)
  // 为内部构建添加提示
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