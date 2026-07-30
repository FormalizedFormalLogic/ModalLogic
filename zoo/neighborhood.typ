// Zoo of the `Neighborhood` logics, generated from `neighborhood.json`
// (which is in turn extracted from the Lean environment by `zoo/Extract.lean`).
//
// Compile from the repository root:
//
//     typst compile --root . zoo/neighborhood.typ zoo/neighborhood.png
#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let edges = json("./neighborhood.json")

// An edge {from: L1, to: L2} means L1 ⊊ L2; draw the arrow from the stronger
// logic to the weaker one, laid out right-to-left (weakest logic rightmost).
#let arrows = edges.map(((from, to)) => strfmt("\"{}\" -> \"{}\"", to, from))

// Every vertex is named `Logic<X>`; label it 𝐗 (bold upright), dropping the prefix.
#let vertices = (edges.map(((from, to)) => from) + edges.map(((from, to)) => to)).dedup()
#let labels = (:)
#for v in vertices {
  labels.insert(v, Logic(v.trim("Logic", at: start)))
}

#figure(caption: [Neighborhood Logic Zoo], numbering: none)[
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
