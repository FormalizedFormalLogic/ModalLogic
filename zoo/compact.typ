// Compact zoo of the `Neighborhood` logics, generated from `compact.json`
// (which is in turn extracted from the Lean environment by `zoo/Extract.lean`).
//
// Unlike `neighborhood.typ`, this one covers only the extensions of E by the
// axioms M, C, N, D, T, B, 4, 5, and shows one representative per equivalence
// class of logics; hence there are no equality edges left to draw.
//
// Compile from the repository root:
//
//     typst compile --root . zoo/compact.typ zoo/compact.png
#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let data = json("./compact.json")

// An edge {from: L1, to: L2, type: t} means L1 ⊊ L2 (t = "ssub", solid) or
// L1 ⊆ L2 (t = "sub", dashed); draw the arrow from the stronger logic to the
// weaker one, laid out right-to-left (weakest logic rightmost).
#let arrows = data.edges.map(((from, to, type)) => {
  if type == "sub" {
    strfmt("\"{}\" -> \"{}\" [style=dashed]", to, from)
  } else {
    strfmt("\"{}\" -> \"{}\"", to, from)
  }
})

// Declare the vertices too, so that a logic no inclusion is known about (its
// only relations being to its own equals, which the compact zoo collapses)
// still shows up.
#let statements = data.nodes.map(v => strfmt("\"{}\";", v)) + arrows

// Every vertex is named `Logic<X>`; label it 𝐗 (bold upright), dropping the prefix.
#let labels = (:)
#for v in data.nodes {
  labels.insert(v, Logic(v.trim("Logic", at: start)))
}

#figure(
  caption: [
    Compact zoo: the extensions of #Logic("E") by #Logic("M"), #Logic("C"), #Logic("N"),
    #Logic("D"), #Logic("T"), #Logic("B"), #Logic("4"), #Logic("5"),
    one representative per equivalence class
  ],
  numbering: none,
)[
  #raw-render(
    raw(
      "
  digraph CompactNeighborhoodLogicsZoo {
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
        + statements.join("\n")
        + "}",
    ),
    labels: labels,
    width: 420pt,
  )
]
