// Usage: #ruby[annotation][base] and #furi[annotation][base].
#let ruby-note(annotation, base, position: top, size: 0.6em) = context {
  let annotation = text(size: size, annotation)
  let annotation-size = measure(annotation)
  let width = calc.max(measure(base).width, annotation-size.width)
  let shift = annotation-size.height + 0.1em

  box(width: width)[
    #align(center, base)
    #place(
      if position == top { top + center } else { bottom + center },
      dy: if position == top { -shift } else { shift },
      annotation,
    )
  ]
}

#let ruby(annotation, base) = ruby-note(annotation, base, position: top)
#let furi(annotation, base) = ruby-note(annotation, base, position: bottom)
