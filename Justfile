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

# Count lines of Lean source per project library (requires cloc)
cloc:
    cloc --include-lang=Lean Fin74/ ModalLogicArchive/

# Remove unused imports/variables and drop unnecessary `public` (run before merging any work)
shake:
    lake shake --keep-public --fix
