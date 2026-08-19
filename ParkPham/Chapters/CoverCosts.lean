import Verso
import VersoManual
import VersoBlueprint
import ParkPham.CoverCosts

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Covering cost" =>

This chapter collects the weighted covering notions and the elementary facts
about them used throughout the main argument.

:::group "cover_costs"
Weights, covering cost, union bounds, and cost under deletion.
:::

:::definition "cover_weight" (parent := "cover_costs") (uses := "set_family") (priority := "high") (lean := "ParkPham.pCost")
For $`p\in[0,1]`, the $`p`-weight of $`\mathcal G` is
$`w_p(\mathcal G)=\sum_{S\in\mathcal G}p^{|S|}`.
:::

:::definition "p_cheap" (parent := "cover_costs") (uses := "cover_weight") (lean := "ParkPham.IsPCheap")
A family $`\mathcal G` is *$`p`-cheap* when
$`w_p(\mathcal G)\leq 1/2`.
:::

:::definition "cover_cost" (parent := "cover_costs") (uses := "covers, cover_weight") (priority := "high") (lean := "ParkPham.coverCost")
The $`p`-covering cost $`f_p(\mathcal H)` is the minimum $`p`-weight among all
families that cover $`\mathcal H`.
:::

:::lemma_ "covers_subfamily" (parent := "cover_costs") (uses := "covers") (effort := "small") (lean := "ParkPham.Covers.of_subset")
If $`\mathcal G` covers $`\mathcal H_2` and
$`\mathcal H_1\subseteq\mathcal H_2`, then $`\mathcal G` also covers
$`\mathcal H_1`.
:::

:::theorem "optimal_cover_exists" (parent := "cover_costs") (uses := "cover_cost") (effort := "small") (lean := "ParkPham.exists_optimal_cover")
Every finite family has a cover whose $`p`-weight is exactly its covering cost.
:::

:::theorem "cover_cost_nonnegative" (parent := "cover_costs") (uses := "cover_cost") (effort := "small") (lean := "ParkPham.coverCost_nonneg")
If $`p\geq0`, then $`f_p(\mathcal H)\geq0`.
:::

:::theorem "cover_cost_monotone" (parent := "cover_costs") (uses := "cover_cost, covers_subfamily") (effort := "small") (lean := "ParkPham.coverCost_mono")
If $`\mathcal H_1\subseteq\mathcal H_2`, then
$`f_p(\mathcal H_1)\leq f_p(\mathcal H_2)`.
:::

:::proof "cover_cost_monotone"
Every cover of $`\mathcal H_2` is also a cover of $`\mathcal H_1`.
:::

:::lemma_ "covers_union" (parent := "cover_costs") (uses := "covers") (effort := "small") (lean := "ParkPham.covers_union")
If $`\mathcal G_i` covers $`\mathcal H_i` for $`i=1,2`, then
$`\mathcal G_1\cup\mathcal G_2` covers
$`\mathcal H_1\cup\mathcal H_2`.
:::

:::lemma_ "cover_weight_union_subadditive" (parent := "cover_costs") (uses := "cover_weight") (effort := "small") (lean := "ParkPham.pCost_union_le")
For $`p\geq0`, union counts shared members only once, so
$`w_p(\mathcal G_1\cup\mathcal G_2)\leq
w_p(\mathcal G_1)+w_p(\mathcal G_2)`.
:::

:::theorem "cover_cost_subadditive" (parent := "cover_costs") (uses := "optimal_cover_exists, covers_union, cover_weight_union_subadditive") (effort := "medium") (priority := "high") (lean := "ParkPham.coverCost_union_le")
For finite families $`\mathcal H_1,\mathcal H_2`,
$`f_p(\mathcal H_1\cup\mathcal H_2)\leq
f_p(\mathcal H_1)+f_p(\mathcal H_2)`.
:::

:::proof "cover_cost_subadditive"
Take optimal covers and use their union as a cover of the union. Its weight is
at most the sum of the two weights.
:::

:::theorem "cover_cost_empty" (parent := "cover_costs") (uses := "cover_cost_nonnegative") (effort := "small") (lean := "ParkPham.coverCost_empty")
$`f_p(\varnothing)=0`.
:::

:::theorem "cover_cost_contains_empty" (parent := "cover_costs") (uses := "cover_cost") (effort := "small")
If $`\varnothing\in\mathcal H`, then $`f_p(\mathcal H)=1`.
:::

:::theorem "bernoulli_union_bound" (parent := "cover_costs") (uses := "bernoulli_measure, upper_closure, cover_weight") (effort := "medium")
For every family $`\mathcal G`,
$`\mu_p(\langle\mathcal G\rangle)\leq w_p(\mathcal G)`.
:::

:::proof "bernoulli_union_bound"
The event that the random set contains at least one member of $`\mathcal G` is
a finite union. Each event indexed by $`S` has probability $`p^{|S|}`.
:::

:::definition "deleted_family" (parent := "cover_costs") (uses := "set_family")
For $`W\subseteq X`, define
$`\mathcal H_W=\{S\setminus W:S\in\mathcal H\}` and its minimal core
$`\mathcal H'_W=\min(\mathcal H_W)`.
:::

:::theorem "deleted_family_cost" (parent := "cover_costs") (uses := "deleted_family, minimal_members_generate, cover_cost") (effort := "medium") (priority := "high")
The deletion operation can only make covering harder:
$`f_p(\mathcal H)\leq f_p(\mathcal H'_W)`.
:::

:::proof "deleted_family_cost"
Every member $`S\setminus W` of the deleted family is contained in its original
member $`S`. A cover of the deleted family therefore covers the original
family; minimalization does not change the upward closure.
:::
