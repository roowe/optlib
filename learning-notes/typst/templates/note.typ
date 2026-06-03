#let note(title: none, subtitle: none, source: none, body) = {
  set document(title: if title == none { "Optlib background note" } else { title })
  set page(
    paper: "a4",
    margin: (x: 24mm, y: 22mm),
    numbering: "1",
  )
  set text(
    lang: "zh",
    region: "CN",
    size: 10.5pt,
  )
  set par(
    leading: 0.72em,
    justify: true,
  )
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    v(0.4em)
    text(size: 20pt, weight: "bold", it.body)
    v(0.5em)
  }
  show heading.where(level: 2): it => {
    v(0.7em)
    text(size: 15pt, weight: "bold", it.body)
    v(0.25em)
  }
  show raw.where(block: true): it => block(
    fill: luma(247),
    inset: 8pt,
    radius: 3pt,
    width: 100%,
    it,
  )

  if title != none {
    align(center)[
      #text(size: 22pt, weight: "bold")[#title]
      #if subtitle != none [
        #v(0.4em)
        #text(size: 11pt, fill: luma(90))[#subtitle]
      ]
      #if source != none [
        #v(0.2em)
        #text(size: 9pt, fill: luma(120))[source: #source]
      ]
    ]
    v(1em)
  }

  body
}

