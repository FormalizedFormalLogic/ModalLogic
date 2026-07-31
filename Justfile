# List available recipes
default:
    @just --list

# Format and regenerate keys of references.bib
format-bib:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Generate the import graph as import_graph.{dot,png,pdf,html} (requires graphviz)
import-graph:
    lake exe graph --to Fin74 import_graph.dot import_graph.png import_graph.pdf import_graph.html

# Regenerate each library's all-import root file (run after adding/removing files)
mk-all:
    # `mk_all --module` without --lib would also try the `ModalLogic` lib declared in
    # lakefile.toml, which has no root file/directory and makes mk_all abort; list the
    # libraries that actually have sources instead (extend when a new project lib is added).
    lake exe mk_all --module --lib Fin74
    lake exe mk_all --module --lib ModalLogicArchive
    lake exe mk_all --module --lib Neighborhood

# Regenerate the Neighborhood logic zoo as zoo/{zoo,status}.json and zoo/zoo.png (requires typst)
zoo:
    lake env lean zoo/Extract.lean
    lake env lean zoo/Status.lean
    typst compile --root . zoo/neighborhood.typ zoo/zoo.png

# Serve the interactive 3D zoo at http://localhost:8080 (requires miniserve; run `just zoo` first)
zoo-serve:
    miniserve zoo --index index.html

# Count lines of Lean source per project library (requires cloc)
cloc:
    cloc --include-lang=Lean Fin74/ Neighborhood/ ModalLogicArchive/

# Remove unused imports/variables and drop unnecessary `public` (slow; usually only needed
# when CI complains). Each library must be shaken in a separate invocation: with no module
# argument shake uses all default targets at once, and loading Fin74 and Neighborhood into
# one environment clashes (both declare `Formula`), which aborts the whole run.
shake:
    lake shake --keep-public --fix Fin74
    lake shake --keep-public --fix ModalLogicArchive
    lake shake --keep-public --fix Neighborhood
