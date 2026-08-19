import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Finite set systems" =>

The entire combinatorial argument takes place over a finite ground set $`X`.
This chapter fixes the vocabulary that will later become the stable Lean API.

:::group "foundations"
Definitions for finite set systems and covers.
:::

:::definition "set_family" (parent := "foundations") (priority := "high")
A *set family* (or hypergraph) on a finite ground set $`X` is a collection
$`\mathcal H \subseteq 2^X`.
:::

:::definition "up_closure" (parent := "foundations") (uses := "set_family") (priority := "high")
The *upward closure* of $`\mathcal H` is
$`\langle\mathcal H\rangle = \{T\subseteq X : \exists S\in\mathcal H,\ S\subseteq T\}`.
:::

:::definition "increasing_family" (parent := "foundations") (uses := "set_family")
A family $`\mathcal F` is *increasing* when membership is preserved on passing
to a superset inside $`X`.
:::

:::proposition "up_closure_increasing" (parent := "foundations") (uses := "up_closure, increasing_family") (effort := "small") (priority := "high")
For every family $`\mathcal H`, its upward closure
$`\langle\mathcal H\rangle` is increasing.
:::

:::proof "up_closure_increasing"
If $`S\in\mathcal H`, $`S\subseteq T`, and $`T\subseteq U`, then transitivity
gives $`S\subseteq U`.
:::

:::definition "minimal_members" (parent := "foundations") (uses := "set_family") (priority := "high")
A member $`S\in\mathcal H` is *minimal* when no proper subset of $`S` belongs
to $`\mathcal H`.  Write $`\min(\mathcal H)` for the family of minimal members.
:::

:::definition "ell_bounded" (parent := "foundations") (uses := "set_family") (priority := "high")
A family is $`\ell`-bounded when every one of its members has cardinality at
most $`\ell`.
:::

:::definition "uniform_level" (parent := "foundations") (uses := "set_family") (priority := "high")
For $`0\leq m\leq |X|`, the $`m`-th level is
$`L_m(X)=\{S\subseteq X: |S|=m\}`.
:::

:::definition "level_density" (parent := "foundations") (uses := "uniform_level")
The density of a family $`\mathcal F` on level $`m` is
$`c_m(\mathcal F)=|\mathcal F\cap L_m(X)|/|L_m(X)|`.
:::

:::definition "cover" (parent := "foundations") (uses := "up_closure") (priority := "high")
A family $`\mathcal G` *covers* $`\mathcal H` when
$`\mathcal H\subseteq\langle\mathcal G\rangle`.
:::

:::definition "cover_weight" (parent := "foundations") (uses := "set_family") (priority := "high")
For $`p\in[0,1]`, the $`p`-weight of $`\mathcal G` is
$`w_p(\mathcal G)=\sum_{S\in\mathcal G}p^{|S|}`.
:::

:::definition "cover_cost" (parent := "foundations") (uses := "cover, cover_weight") (priority := "high")
The $`p`-covering cost $`f_p(\mathcal H)` is the minimum $`p`-weight among all
families that cover $`\mathcal H`.
:::

:::definition "bernoulli_measure" (parent := "foundations") (uses := "set_family")
The $`p`-biased Bernoulli measure $`\mu_p` on $`2^X` samples each element of
$`X` independently with probability $`p`.
:::
