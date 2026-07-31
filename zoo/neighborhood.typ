// Zoo of the `Neighborhood` logics, generated from `zoo.json`
// (which is in turn extracted from the Lean environment by `zoo/Extract.lean`).
//
// Compile from the repository root:
//
//     typst compile --root . zoo/neighborhood.typ zoo/zoo.png
#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let edges = json("./zoo.json")

// An edge {from: L1, to: L2, type: t} means L1 ⊊ L2 (t = "ssub", solid),
// L1 ⊆ L2 (t = "sub", dashed) or L1 = L2 (t = "eq", arrowless double line);
// draw the arrow from the stronger logic to the weaker one, laid out
// right-to-left (weakest logic rightmost).
#let arrows = edges.map(((from, to, type)) => {
  if type == "ssub" {
    strfmt("\"{}\" -> \"{}\"", to, from)
  } else if type == "sub" {
    strfmt("\"{}\" -> \"{}\" [style=dashed]", to, from)
  } else if type == "eq" {
    (
      strfmt("\"{}\" -> \"{}\" [color=\"black:white:black\" arrowhead=\"none\"]", to, from),
      strfmt("{{rank = same; \"{}\"; \"{}\";}}", to, from),
    ).join("\n")
  }
})

// Every vertex is named `Logic<X>`; label it 𝐗 (bold upright), dropping the prefix.
#let vertices = (edges.map(((from, to)) => from) + edges.map(((from, to)) => to)).dedup()
#let labels = (:)
#for v in vertices {
  labels.insert(v, Logic(v.trim("Logic", at: start)))
}

#figure(caption: [Modal logic characterlized neighborhood semantics zoo], numbering: none)[
  #raw-render(
    raw(
      "
  digraph NeighborhoodLogicsZoo {
    rankdir = RL;

    node [
      shape=none
      margin=0.125
      width=0
      height=0
    ]

    edge [
      style = solid
      arrowhead = vee
      arrowsize = 0.75
    ];

  "
        + arrows.join("\n")
        + "}",
    ),
    labels: labels,
    width: 480pt,
  )
]
