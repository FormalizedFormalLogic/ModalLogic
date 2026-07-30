# References

Every result taken from the literature is cited in its docstring by the BibTeX key of an entry in [references.bib](../references.bib); the format of those citations is described in [style.md](./style.md#references-and-citations).

## Adding an entry

After adding or editing an entry, always reformat and regenerate the keys:

```shell
just format-bib
```

Keys follow the AMS (MathSciNet/MRef) scheme — `Bek90`, `AB05`, `dJY11`, keeping the lowercase initial of a von part in a multi-author key. The exact rules live in [`.bibtoolrsc`](../.bibtoolrsc) (`key.format`, `fmt.name.name`, `new.format.type`); do not adjust a key by hand, take whatever `just format-bib` produces.

`key.format` cannot express one case: for a **single author with a von part** it drops the von part and uses the first three letters of the surname (`van Benthem` → `Ben`), where the convention is `vB`. Pin the key explicitly with a `bibkey` field, which takes precedence, and then run bibtool:

```bibtex
@Article{Ben78,
  bibkey        = {vB78},
  author        = {van Benthem, J. F. A. K.},
  ...
}
```

## PDFs

The PDFs of the cited papers are kept out of the repository, in the ignored directory `.claude/docs/references/`, named after their BibTeX key (`<key>.pdf`). Whenever a key is regenerated, rename the corresponding file to match. Unpublished material — personal notes, blog posts, repository memos — goes to `.claude/docs/references/unpublished/` and gets no entry in `references.bib`.
