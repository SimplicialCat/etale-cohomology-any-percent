#import "@preview/ctheorems:1.1.3" as C
#import "void-style.typ": void-style-heading-numbering

#let insert-qed = C.thm-qed-done.update(false)
#let suppress-qed = C.thm-qed-done.update(true)

/*
[Note] All-in-one state dictionary

https://typst.app/docs/reference/introspection/state/#caution dictates that: 
  In general, you should try not to generate state updates from within context expressions. 
  If possible, try to express your updates as non-contextual values or functions that compute the new value from the previous value. 
 
When updating the background color stack, we need to access the nesting depth. 
If we had two separate state variables for nesting depth and color stack, we need to
 write something like: 

`thm-box-curr-bg.update(arr => arr.push(some-computation(nesting-state.get())))`

But then `nesting-state.get()` requires a context, so we would be generating a state update from a context expression. This makes the document diverge. In fact, before we refactored these 2 states into 1, the document indeed stayed divergent. Let's see what we gain from packing 2 states into 1. We may now write: 

```
vthm-state-dict.update(dict => {
  dict.thm-box-curr-bg.push(some-computation(dict.nesting-state))
  dict
})
```
This gives a *non-contextual* state update that does the same thing. The document now converges. Compilication time is reduced to 1/3 of original, and preview update time is also reduced by that much. 
*/
#let vthm-state-dict = state("vthm-state-dict", (
  nesting-state: 1, 
  thm-box-curr-bg: (rgb("#ffffff"),)
))

#let amplify-color(color, magnitude) = {
  if (magnitude >= 1.0) {return color}
  if (magnitude <= 0.0) {return rgb("#ffffff")}
  return rgb(..rgb(color).components().map(x => {
    let y = 100% - (100% - x) * magnitude
    return y
  }))
}
  
#let color-config(key) = {
  import "void-config.typ": compile-cfg
  let print-mode = compile-cfg.print-mode
  if not print-mode {(
    theorem-color: depth => amplify-color(rgb("#ffff90"), calc.pow(0.5, depth - 1)),
    proposition-color: depth => amplify-color(rgb("#a0ffa0"), calc.pow(0.5, depth - 1)),
    lemma-color: depth => amplify-color(rgb("#b0b0ff"), calc.pow(0.5, depth - 1)),
    properties-color: depth => amplify-color(rgb("#c2eb90"), calc.pow(0.5, depth - 1)),
    corollary-color: depth => amplify-color(rgb("#a0ffff"), calc.pow(0.5, depth - 1)),
    remark-color: depth => amplify-color(rgb("ffbbdd"), calc.pow(0.5, depth - 1)),
    notation-color: depth => amplify-color(rgb("ffddbb"), calc.pow(0.5, depth - 1)),
    example-color: depth => amplify-color(rgb("#e4beff"), calc.pow(0.5, depth - 1)),
    definition-color: depth => amplify-color(rgb("ffbbbb"), calc.pow(0.5, depth - 1)),
    construction-color: depth => amplify-color(rgb("#ffe0bb"), calc.pow(0.5, depth - 1)),
    observation-color: depth => amplify-color(rgb("#e6c5ff"), calc.pow(0.5, depth - 1)),
    problem-color: depth => amplify-color(rgb("ff99cc"), calc.pow(0.5, depth - 1)),
    exercise-color: depth => amplify-color(rgb("ff99cc"), calc.pow(0.5, depth - 1)),
    proof-color: depth => amplify-color(rgb("e7e7e7"), 0.6 / calc.max(depth, 1)),
    date-color: depth => rgb("ffffff"),
  ).at(key)} else {
    depth => rgb("#00000000")
  }
}

// #let nesting-depth-state = state("nesting-depth", 0)
// #let curr-fill-state = state("curr-fill", rgb("#00000000"))

#let thm-box-curr-color() = vthm-state-dict.get().thm-box-curr-bg.last()
// #let thm-box-curr-color() = curr-fill-state.get()

#let vthm-std-box(identifier: "theorem", head, color-id: none, generator: C.thmbox, reset-qed: false, ..args) = (name: none, body) => {
  if name != none and type(name) != label {
    panic("name can only be none or label")
  }
  let color-id2 = if (color-id == none) {lower(head)} else {color-id}
  vthm-state-dict.update(
    dict => {
      let curr-fill = color-config(color-id2 + "-color")(dict.nesting-state)
      dict.thm-box-curr-bg.push(curr-fill)
      dict.nesting-state += 1
      dict
    }
  )
  // nesting-depth-state.update(x => x + 1)
  // let curr-fill() = color-config(color-id2 + "-color")(nesting-depth-state.get())
  // let old-fill() = curr-fill-state.get()
  // context curr-fill-state.update(curr-fill())
  context [
    #generator(identifier, head, 
      fill: thm-box-curr-color(), 
      stroke: black, 
      width: 100% - 0pt,
      inset: (x: 6pt, y: 8pt), 
      breakable: true, 
      ..args.named()
    )(body, 
      ..if (generator == C.thmbox) {(numbering: void-style-heading-numbering.with(last-dot: false))}
    )
    #name
    // https://typst.app/docs/reference/foundations/label/: Currently, labels can only be attached to elements in markup mode, not in code mode. This might change in the future.
  ]
  if (reset-qed) {
    insert-qed
  }
  vthm-state-dict.update(
    dict => {
      dict.thm-box-curr-bg = dict.thm-box-curr-bg.slice(0, -1)
      dict.nesting-state -= 1
      dict
    }
  )
  // context curr-fill-state.update(old-fill())
  // nesting-depth-state.update(x => x - 1)
}
#let theorem = vthm-std-box("Theorem")
#let lemma = vthm-std-box("Lemma")
#let problem = vthm-std-box(identifier: "problem", "Problem")
#let remark = vthm-std-box("Remark")
#let definition = vthm-std-box("Definition")

#let example = vthm-std-box("Example")
#let notation = vthm-std-box("Notation")
#let properties = vthm-std-box("Properties")
#let exercise = vthm-std-box("Exercise")
#let observation = vthm-std-box("Observation")
#let construction = vthm-std-box("Construction")
#let proposition = vthm-std-box("Proposition")
#let question = vthm-std-box("Question", color-id: "example")
#let fact = vthm-std-box("Fact", color-id: "lemma")

#let proof = vthm-std-box(identifier: "proof", "Proof", generator: C.thmproof, reset-qed: true)
#let proof_(head, body) = vthm-std-box(identifier: "proof", head, color-id: "proof", generator: C.thmproof, reset-qed: true)(body)
#let date(body) = vthm-std-box(identifier: "proof", none, color-id: "date", generator: C.thmproof, separator: none)([
  #C.thm-qed-done.update(true)
  #align(center, body)
])
#let corollary = vthm-std-box("Corollary")