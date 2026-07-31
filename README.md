# Redesign Modal Logic

Test project for modal logic redesigning.

## Zoo

Strict inclusions between the logics formalized in `Neighborhood`, extracted from the Lean environment and reduced by transitivity (regenerated on every push to `main`; see `zoo/`).

**[Interactive 3D zoo](https://formalizedformallogic.github.io/ModalLogic/)** — the zoo as a rotatable 3D Hasse diagram: equal logics are merged into one node, node color encodes deductive strength, hovering a logic highlights its direct neighbours, and a search box flies to a given logic. Locally, run `just zoo` and then `just zoo-serve`.

The static 2D rendering ([PNG](https://formalizedformallogic.github.io/ModalLogic/neighborhood.png)):

![Neighborhood logic zoo](https://formalizedformallogic.github.io/ModalLogic/neighborhood.png)
