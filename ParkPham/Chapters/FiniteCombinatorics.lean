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
Reusable lemmas about minimal families, levels, and covering cost.
:::

:::theorem "minimal_members_generate" (parent := "finite_combinatorics") (uses := "minimal_members, up_closure") (effort := "medium") (priority := "high")
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

:::theorem "level_density_monotone" (parent := "finite_combinatorics") (uses := "increasing_family, level_density") (effort := "medium") (priority := "high")
If $`\mathcal F` is increasing and $`m<|X|`, then
$`c_m(\mathcal F)\leq c_{m+1}(\mathcal F)`.
:::

:::proof "level_density_monotone" (uses := "uniform_level")
Double-count pairs $`(A,B)` with $`A\in\mathcal F\cap L_m(X)`,
$`B\in L_{m+1}(X)`, and $`A\subset B`.
:::

:::theorem "cover_cost_monotone" (parent := "finite_combinatorics") (uses := "cover_cost") (effort := "small")
If $`\mathcal H_1\subseteq\mathcal H_2`, then
$`f_p(\mathcal H_1)\leq f_p(\mathcal H_2)`.
:::

:::proof "cover_cost_monotone"
Every cover of $`\mathcal H_2` is also a cover of $`\mathcal H_1`.
:::

:::theorem "cover_cost_subadditive" (parent := "finite_combinatorics") (uses := "cover_cost") (effort := "medium") (priority := "high")
For finite families $`\mathcal H_1,\mathcal H_2`,
$`f_p(\mathcal H_1\cup\mathcal H_2)\leq
f_p(\mathcal H_1)+f_p(\mathcal H_2)`.
:::

:::proof "cover_cost_subadditive"
Take optimal covers and use their union as a cover of the union.  Its weight is
at most the sum of the two weights.
:::

:::theorem "cover_cost_empty" (parent := "finite_combinatorics") (uses := "cover_cost") (effort := "small")
$`f_p(\varnothing)=0`.
:::

:::theorem "cover_cost_contains_empty" (parent := "finite_combinatorics") (uses := "cover_cost") (effort := "small")
If $`\varnothing\in\mathcal H`, then $`f_p(\mathcal H)=1`.
:::

:::theorem "bernoulli_union_bound" (parent := "finite_combinatorics") (uses := "bernoulli_measure, up_closure, cover_weight") (effort := "medium")
For every family $`\mathcal G`,
$`\mu_p(\langle\mathcal G\rangle)\leq w_p(\mathcal G)`.
:::

:::proof "bernoulli_union_bound"
The event that the random set contains at least one member of $`\mathcal G` is
a finite union.  Each event indexed by $`S` has probability $`p^{|S|}`.
:::

:::definition "deleted_family" (parent := "finite_combinatorics") (uses := "set_family")
For $`W\subseteq X`, define
$`\mathcal H_W=\{S\setminus W:S\in\mathcal H\}` and its minimal core
$`\mathcal H'_W=\min(\mathcal H_W)`.
:::

:::theorem "deleted_family_cost" (parent := "finite_combinatorics") (uses := "deleted_family, minimal_members_generate, cover_cost") (effort := "medium") (priority := "high")
The deletion operation can only make covering harder:
$`f_p(\mathcal H)\leq f_p(\mathcal H'_W)`.
:::

:::proof "deleted_family_cost"
Every member $`S\setminus W` of the deleted family is contained in its original
member $`S`.  A cover of the deleted family therefore covers the original
family; minimalization does not change the upward closure.
:::
