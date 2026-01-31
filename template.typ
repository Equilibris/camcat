#import "@preview/codly:1.3.0": *
#import "@preview/codly-languages:0.1.8": *

// The project function defines how your document looks.
// It takes your content and some metadata and formats it.
// Go ahead and customize it to your liking!
#let project(title: "", authors: (), body) = {
  // Set the document's basic properties.
  set document(author: authors.map(a => a.name), title: title)
  set page(numbering: "1", number-align: center)
  set text(font: "New Computer Modern", lang: "en")
  set heading(numbering: "1.")
  show math.equation: set text(weight: 400)

  show: codly-init.with()
  codly(languages: codly-languages)

  show heading.where(
    level: 2
  ): it => text(
    size: 11pt,
    weight: "bold",
    style: "normal",
    it.body + [.],
  )

  set par(leading: 0.58em)

  // Title row.
  align(center)[
    #block(text(weight: 700, 1.75em, title))
  ]

  // Author information.
  pad(
    top: 0.3em,
    bottom: 0.3em,
    x: 2em,
    grid(
      columns: (1fr,) * calc.min(3, authors.len()),
      gutter: 1em,
      ..authors.map(author => align(center)[
        *#author.name* \
        #author.email
      ]),
    ),
  )

  // Main body.
  set par(justify: true)

  body
}
