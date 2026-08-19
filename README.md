# Lean Park–Pham formalization

This repository is a Lean 4 project and a Verso Blueprint for formalizing the
Park–Pham expectation-threshold theorem.  The main combinatorial route follows
Tran and Vu's short inductive proof.

## What the blueprint does

Each definition, lemma, theorem, or corollary has a stable label.  A `uses`
edge records a genuine mathematical dependency between two labels.  Nodes do
not need corresponding Lean code yet: this lets the graph serve as a research
plan before formalization begins.

As Lean declarations are attached to labels, Verso Blueprint computes their
status, including whether a declaration still contains `sorry`.  The rendered
site includes both an interactive dependency graph and a progress summary.

## Build

```bash
lake update
lake exe cache get
lake exe vbp build
```

The HTML site is written to `_out/site/html-multi/`.  To build and serve it:

```bash
lake exe vbp build --serve
```

Useful planning queries include:

```bash
lake exe vbp query work-queue
lake exe vbp query metadata
```

## Layout

- `ParkPham/FiniteSetSystems.lean`: formal finite-set-family API
- `ParkPham/Chapters/Foundations.lean`: foundational blueprint definitions
- `ParkPham/Chapters/FiniteCombinatorics.lean`: minimal-family and level lemmas
- `ParkPham/Chapters/CoverCosts.lean`: covering costs and their basic properties
- `ParkPham/Chapters/Covering.lean`: Tran–Vu's double count and induction
- `ParkPham/Chapters/Threshold.lean`: passage to the expectation threshold
- `ParkPham/Blueprint.lean`: assembled document, graph, and summary
- `ParkPhamMain.lean`: site generator

The first implementation milestone is the foundations chapter, followed by
`level_density_monotone` and `minimal_members_generate`.
