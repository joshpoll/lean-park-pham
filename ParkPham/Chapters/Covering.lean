import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Tran–Vu covering argument" =>

This is the combinatorial heart of the project.  Constants are initially kept
close to the short proof; after the main route compiles, the optimized
$`3.998\ldots` argument can be added as a separate branch.

:::group "covering_argument"
The double-counting estimate and the induction it powers.
:::

:::definition "large_small_split" (parent := "covering_argument") (uses := "deleted_family, ell_bounded") (priority := "high")
Assume $`\mathcal H` is $`\ell`-bounded.  Split the minimal deleted family as
$`\mathcal H'_W=\mathcal G_W\cup\widetilde{\mathcal H}_W`, where
$`\mathcal G_W` consists of members larger than $`9\ell/10`.  Consequently
$`\widetilde{\mathcal H}_W` is $`\lfloor9\ell/10\rfloor`-bounded.
:::

:::lemma_ "minimal_deleted_set_count" (parent := "covering_argument") (uses := "large_small_split, minimal_members") (effort := "large") (priority := "high")
Fix $`k>9\ell/10`.  After fixing a union $`W'=W\cup S'` that contains an
edge $`S\in\mathcal H`, every minimal remainder $`S'\in\mathcal G_W` of size
$`k` must be a subset of $`S`.  Hence there are at most
$`\binom{\ell}{k}` possible remainders.
:::

:::proof "minimal_deleted_set_count"
If $`S'` is not contained in $`S`, then $`S'\cap S=S\setminus W` is a strictly
smaller member of the deleted family, contradicting minimality of $`S'`.
:::

:::lemma_ "binomial_ratio_bound" (parent := "covering_argument") (uses := "uniform_level") (effort := "large") (priority := "high")
For the parameter range in the covering theorem and
$`w=\lfloor Lp|X|/10\rfloor`, bound the ratio
$`\binom{|X|}{w+k}/\binom{|X|}{w}` by the geometric factor required in the
double-counting estimate.
:::

:::lemma_ "double_counting_lemma" (parent := "covering_argument") (uses := "minimal_deleted_set_count, binomial_ratio_bound, bernoulli_union_bound, large_small_split") (effort := "large") (priority := "high")
For $`L>1000` and $`w=\lfloor Lp|X|/10\rfloor`, the sum over all
$`W\in L_w(X)` of $`\mu_p(\langle\mathcal G_W\rangle)` is at most
$`\binom{|X|}{w}/(8\cdot16^\ell)`.
:::

:::proof "double_counting_lemma"
Use the Bernoulli union bound, group minimal remainders by their cardinality,
and count pairs $`(W,S')` by first choosing $`W\cup S'`.  Apply
{uses "minimal_deleted_set_count"}[] and then sum the resulting geometric
estimate over $`9\ell/10<k\leq\ell`.
:::

:::lemma_ "many_good_deletions" (parent := "covering_argument") (uses := "double_counting_lemma") (effort := "medium") (priority := "high")
All but at most a $`1/(2\cdot8^\ell)` fraction of the $`w`-sets $`W` have
$`f_p(\mathcal G_W)\leq 1/(2\cdot16^{\ell+2})`.
:::

:::proof "many_good_deletions"
Apply averaging to the sum in the double-counting lemma, using the family
$`\mathcal G_W` itself as a cover.
:::

:::lemma_ "small_part_retains_cost" (parent := "covering_argument") (uses := "many_good_deletions, deleted_family_cost, cover_cost_subadditive, large_small_split") (effort := "medium") (priority := "high")
For every good $`W`, if $`f_p(\mathcal H)` exceeds the inductive threshold,
then $`f_p(\widetilde{\mathcal H}_W)` exceeds the corresponding threshold at
$`\lfloor9\ell/10\rfloor`.
:::

:::proof "small_part_retains_cost"
The deleted minimal family has cost at least that of $`\mathcal H`.  Remove the
small covering cost of $`\mathcal G_W` using subadditivity.
:::

:::lemma_ "inductive_level_arithmetic" (parent := "covering_argument") (uses := "uniform_level") (effort := "large") (priority := "high")
With $`m_\ell=\lfloor Lp|X|\log_2(\ell+1)\rfloor`, the level reached by applying
the induction hypothesis on $`X\setminus W` and then adjoining $`W` is no
larger than $`m_\ell`.
:::

:::theorem "tran_vu_covering_theorem" (parent := "covering_argument") (uses := "cover_cost_contains_empty, small_part_retains_cost, inductive_level_arithmetic, level_density_monotone") (effort := "large") (priority := "high")
For a sufficiently large universal $`L`, let
$`m_\ell=\lfloor Lp|X|\log_2(\ell+1)\rfloor`.  If $`\mathcal H` is
$`\ell`-bounded and its covering cost exceeds the strengthened inductive
threshold, then $`\langle\mathcal H\rangle` occupies more than the corresponding
strengthened fraction of $`L_{m_\ell}(X)`.
:::

:::proof "tran_vu_covering_theorem"
Induct simultaneously on $`\ell` and $`|X|`.  The case $`\ell=0` follows from
{uses "cover_cost_contains_empty"}[the empty-set cost lemma].  For the step,
average over good deletion sets, apply the induction hypothesis to each small
part, adjoin the deletion set, and finally use monotonicity of level density.
:::

:::corollary "park_pham_covering_corollary" (parent := "covering_argument") (uses := "tran_vu_covering_theorem") (effort := "small") (priority := "high")
For a universal $`L`, if $`\mathcal H` is $`\ell`-bounded and
$`f_p(\mathcal H)>1/2`, then its upward closure occupies more than $`2/3` of
level $`\lfloor Lp|X|\log_2(\ell+1)\rfloor`.
:::
