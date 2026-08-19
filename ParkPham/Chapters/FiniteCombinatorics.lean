import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Finite combinatorial infrastructure" =>

These lemmas isolate the parts of the proof that should be useful independently
of the final numerical estimates.

:::group "finite_combinatorics"
Reusable lemmas about minimal families and levels.
:::

:::theorem "minimal_members_generate" (parent := "finite_combinatorics") (uses := "minimal_members, upper_closure") (effort := "medium") (priority := "high")
Every family on a finite ground set has the same upward closure as its minimal
members:
$`\langle\min(\mathcal H)\rangle=\langle\mathcal H\rangle`.
:::

:::proof "minimal_members_generate"
One inclusion is immediate.  For the other, among the members of $`\mathcal H`
contained in a fixed member, choose one of minimum cardinality.
:::

:::theorem "minimal_members_preserve_boundedness" (parent := "finite_combinatorics") (uses := "minimal_members, ell_bounded") (effort := "small")
If $`\mathcal H` is $`\ell`-bounded, then so is $`\min(\mathcal H)`.
:::

:::proof "minimal_members_preserve_boundedness"
Minimal members are members.
:::

:::theorem "level_density_monotone" (parent := "finite_combinatorics") (uses := "is_upper_set, level_density") (effort := "medium") (priority := "high")
If $`\mathcal F` is increasing and $`m<|X|`, then
$`c_m(\mathcal F)\leq c_{m+1}(\mathcal F)`.
:::

:::proof "level_density_monotone" (uses := "uniform_level")
Double-count pairs $`(A,B)` with $`A\in\mathcal F\cap L_m(X)`,
$`B\in L_{m+1}(X)`, and $`A\subset B`.
:::
