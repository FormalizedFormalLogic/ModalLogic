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
// weaker one, laid out top-to-bottom (E at the bottom, the strongest logics
// at the top).
#let arrows = data.edges.map(((from, to, type)) => {
  if type == "sub" {
    strfmt("\"{}\" -> \"{}\" [style=dashed]", to, from)
  } else {
    strfmt("\"{}\" -> \"{}\"", to, from)
  }
})

// Pin every logic of a given level -- the length of the longest chain of
// inclusions below it, as computed by `zoo/Extract.lean` -- to one row. This
// is what makes the drawing a graded Hasse diagram: without it the layout
// engine ranks by its own criterion, and covers that skip several levels drag
// their endpoints across the picture, which is most of what makes the full
// zoo hard to read. Declaring the rows also declares the vertices, so a logic
// no inclusion is known about (its only relations being to its own equals,
// which the compact zoo collapses) still shows up.
#let byLevel = (:)
#for v in data.nodes {
  let k = str(v.level)
  byLevel.insert(k, byLevel.at(k, default: ()) + (v.name,))
}
#let rows = byLevel.values().map(vs => strfmt(
  "{{rank = same; {}}}",
  vs.map(v => strfmt("\"{}\";", v)).join(" "),
))

// Every vertex is named `Logic<X>`; label it 𝐗 (bold upright), dropping the prefix.
#let labels = (:)
#for v in data.nodes {
  labels.insert(v.name, Logic(v.name.trim("Logic", at: start)))
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
    rankdir = TB;
    // `rank = same` groups are only honoured across the whole graph with this.
    newrank = true;
    // Room to breathe, and a generous crossing-minimisation budget: the graph
    // is small enough that the extra passes cost nothing worth measuring.
    nodesep = 0.3;
    ranksep = 1.8;
    mclimit = 40;

    node [
      shape=none
      margin=0.125
      width=0.5
      height=0.5
    ]

    edge [
      style = solid
      arrowhead = vee
      arrowsize = 0.75
    ];

  "
        + (rows + arrows).join("\n")
        + "}",
    ),
    labels: labels,
    width: 960pt,
  )
]
