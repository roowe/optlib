# Typst Notes

This is the Typst workspace for Optlib background notes.

Compile one note:

```sh
typst compile notes/convex-basic.typ build/convex-basic.pdf
```

Compile all migrated notes from the repository root:

```sh
typst compile learning-notes/typst/notes/convex-basic.typ learning-notes/typst/build/convex-basic.pdf
typst compile learning-notes/typst/notes/mathlib-linear-algebra.typ learning-notes/typst/build/mathlib-linear-algebra.pdf
typst compile learning-notes/typst/notes/mathlib-finite-dimension.typ learning-notes/typst/build/mathlib-finite-dimension.pdf
typst compile learning-notes/typst/notes/pilp-lesson.typ learning-notes/typst/build/pilp-lesson.pdf
```

The current four notes were mechanically migrated from earlier HTML notes with
Pandoc. They compile, but still keep some HTML-origin structure. Future notes
should use `templates/note.typ` as the starting point.

