#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge, interpret-marks-arg

#let state-scdh-curr-stage = state("state-scdh-curr-stage", 0)
// #let state-scdh-curr-breakpts = state("state-scdh-curr-breakpts", (:))

#let send-stage(stage) = state-scdh-curr-stage.update(stage)

#let stepping-color = red
#let deducing-color = blue

#let node2(absent: false, color: none, ..args) = {
  let pargs = args.pos()
  let nargs = args.named()

  if (absent) {
    return none
  }

  if (color != none) {
    /*
    if ("label" not in nargs and pargs.len() >= 2) {
      let lab = pargs.remove(1)
      nargs.insert("label", lab)
    }
    if ("label" in nargs) {
      let lab2 = text(nargs.label, fill: color)
      nargs.insert("label", lab2)
    }
    */
    // turns out fletcher-0.5.8 does not support named argument label for node()
    // I'll just modify the 2nd positional argument
    if pargs.len() >= 2 {
      let lab2 = text(pargs.at(1), fill: color)
      pargs.at(1) = lab2
    }
  }
  return node(..pargs, ..nargs)
}

#let dictionary-stroke(strk) = {
  return (
    paint: strk.paint, 
    thickness: strk.thickness, 
    cap: strk.cap, 
    join: strk.join, 
    dash: strk.dash, 
    miter-limit: strk.miter-limit
  )
}

#let edge2(absent: false, color: none, tail-color: none, ..args) = {
  let pargs = args.pos()
  let nargs = args.named()

  if (absent) {
    return none
  }

  if ("label-side" not in nargs) {
    nargs.insert("label-side", center)
  }

  if (color != none) {
    if ("label" not in nargs) {
      for (ind, parg) in array.zip(range(pargs.len()), pargs) {
        if type(parg) == content {
          let _ = pargs.remove(ind)
          nargs.insert("label", parg)
          break
        }
      }
    }
    if ("label" in nargs) {
      nargs.insert("label", text(nargs.label, fill: color))
    }

    nargs.insert("stroke", {
      let strk = nargs.at("stroke", default: stroke())
      strk = stroke(
        ..dictionary-stroke(strk), 
        ..(paint: color)
      )
      strk
    })
  }

  if (tail-color != none) {
    if ("marks" not in nargs) {
      for (ind, parg) in array.zip(range(pargs.len()), pargs) {
        if type(parg) == str and parg != parg.find(regex("[lrudtbnesw,]+")) {
          let _ = pargs.remove(ind)
          let mks = interpret-marks-arg(parg)
          nargs += mks
        }
      }
    }

    if ("marks" in nargs) {
      let mks = nargs.marks
      let (minPos, minInd, minMk) = (114514.0, -1, none)
      for (ind, mk) in array.zip(range(mks.len()), mks) {
        if (mk.pos <= minPos) {
          minPos = mk.pos
          minMk = mk
          minInd = ind
        }
      }
      let strk = minMk.at("stroke", default: (:))
      strk.insert("paint", tail-color)
      minMk.insert("stroke", strk)
      mks.at(minInd) = minMk
      nargs.insert("marks", mks)
    }
  }
  return edge(..pargs, ..nargs)
}

#let anim-dict-positive = (
  ab: (absent: true), 
  pr: (absent: false), 
  cs: (color: stepping-color), 
  cd: (color: deducing-color), 
  ts: (tail-color: stepping-color), 
  td: (tail-color: deducing-color), 
  p: true
)
#let anim-dict-negative = {
  let d = (:)
  for (k, _) in anim-dict-positive {
    d.insert(k, none)
  }
  d += (p: false)
  d
}

#let cmp-funcs = (
  ge: k => s => s >= k, 
  le: k => s => s <= k, 
  g: k => s => s > k,
  l: k => s => s < k,
  e: k => s => s == k, 
  ne: k => s => s != k
)
#let choose-anim-dict(flag) = if (flag) {anim-dict-positive} else {anim-dict-negative}
#let generate-anim-func(cmp) = k => {
  let s = state-scdh-curr-stage.get()
  let d = choose-anim-dict(cmp(k)(s))
  return d
}
#let ge = generate-anim-func(cmp-funcs.ge)
#let le = generate-anim-func(cmp-funcs.le)
#let g = generate-anim-func(cmp-funcs.g)
#let l = generate-anim-func(cmp-funcs.l)
#let e = generate-anim-func(cmp-funcs.e)
#let ne = generate-anim-func(cmp-funcs.ne)

#let flip-pair(arr) = { let (u, v) = arr; return (v, u) }