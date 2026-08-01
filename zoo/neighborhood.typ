// Zoo of the `Neighborhood` logics, generated from `zoo.json`
// (which is in turn extracted from the Lean environment by `zoo/Extract.lean`).
//
// Compile from the repository root:
//
//     typst compile --root . zoo/neighborhood.typ zoo/zoo.png
#import "template.typ": *

#set page(width: auto, height: auto, margin: 24pt)

#let data = json("./zoo.json")

// Equal logics are merged into one vertex, labelled 𝐋 with a superscript
// +n counting the further logics equal to it -- the same convention as the
// interactive zoo. Drawing the equalities instead would not survive the size
// of the classes: the largest holds fifty-odd logics, over half of them equal
// to `EMT5` alone, and no arrangement of a row of that many keeps the lines
// between them short.
#let classes = (:)
#for v in data.nodes {
  classes.insert(v.rep, classes.at(v.rep, default: (level: v.level, members: ())))
  classes.at(v.rep).members.push(v.name)
}

#let labels = (:)
#for (rep, cls) in classes {
  let name = Logic(rep.trim("Logic", at: start))
  let extra = cls.members.len() - 1
  labels.insert(rep, if extra == 0 { name } else { $name^(+#extra)$ })
}

// An edge {from: L1, to: L2, type: t} means L1 ⊊ L2 (t = "ssub", solid),
// L1 ⊆ L2 (t = "sub", dashed) or L1 = L2 (t = "eq", which the merge absorbs);
// draw the arrow from the stronger logic to the weaker one, laid out
// top-to-bottom (E at the bottom, the strongest logics at the top).
//
// Projecting the inclusions onto the classes leaves them transitively reduced
// already, so no edge here is implied by the others -- this really is the
// Hasse diagram of the merged order.
#let repOf = (:)
#for v in data.nodes {
  repOf.insert(v.name, v.rep)
}
#let seen = (:)
#let arrows = ()
#for (from, to, type) in data.edges {
  let (a, b) = (repOf.at(to), repOf.at(from))
  let key = a + " " + b
  if type != "eq" and a != b and not seen.at(key, default: false) {
    seen.insert(key, true)
    arrows.push(
      if type == "sub" {
        strfmt("\"{}\" -> \"{}\" [style=dashed]", a, b)
      } else {
        strfmt("\"{}\" -> \"{}\"", a, b)
      },
    )
  }
}

// Pin every class of a given level -- the length of the longest chain of
// inclusions below it, as computed by `zoo/Extract.lean` -- to one row. This
// is what makes the drawing a graded Hasse diagram: without it the layout
// engine ranks by its own criterion, and covers that skip several levels drag
// their endpoints across the picture.
#let byLevel = (:)
#for (rep, cls) in classes {
  let k = str(cls.level)
  byLevel.insert(k, byLevel.at(k, default: ()) + (rep,))
}
#let rows = byLevel.values().map(vs => strfmt(
  "{{rank = same; {}}}",
  vs.map(v => strfmt("\"{}\";", v)).join(" "),
))

#figure(
  caption: [
    Modal logic characterlized neighborhood semantics zoo;
    $#Logic("L")^(+n)$ merges $n$ further logics equal to #Logic("L")
  ],
  numbering: none,
)[
  #raw-render(
    raw(
      "
  digraph NeighborhoodLogicsZoo {
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
    width: 1200pt,
  )
]
