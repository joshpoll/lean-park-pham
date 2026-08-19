import Verso
import VersoManual
import VersoBlueprint
import ParkPham.CoverCosts

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "From covers to thresholds" =>

The covering theorem is finite and combinatorial.  This chapter supplies the
probabilistic bridge to the usual statement of the Park–Pham theorem.

:::group "threshold_bridge"
Expectation thresholds, critical thresholds, and the final implication.
:::

:::definition "p_small" (parent := "threshold_bridge") (uses := "covers, p_cheap") (priority := "high") (lean := "ParkPham.IsPSmall")
A family $`\mathcal F` is *$`p`-small* if it has a cover $`\mathcal G` with
$`w_p(\mathcal G)\leq 1/2`.
:::

:::definition "expectation_threshold" (parent := "threshold_bridge") (uses := "p_small") (priority := "high")
The expectation threshold $`q(\mathcal F)` is the supremum of the parameters
$`p` for which $`\mathcal F` is $`p`-small.
:::

:::definition "critical_threshold" (parent := "threshold_bridge") (uses := "bernoulli_measure, is_upper_set") (priority := "high")
For a nontrivial increasing family $`\mathcal F`, its critical threshold
$`p_c(\mathcal F)` is the unique parameter at which
$`\mu_p(\mathcal F)=1/2`, equivalently an appropriate infimum if uniqueness is
not yet available.
:::

:::theorem "expectation_threshold_lower_bound" (parent := "threshold_bridge") (uses := "expectation_threshold, critical_threshold, bernoulli_union_bound") (effort := "medium")
$`q(\mathcal F)\leq p_c(\mathcal F)` for every nontrivial increasing family.
:::

:::proof "expectation_threshold_lower_bound"
A cheap cover and the Bernoulli union bound show that the probability of the
family is at most $`1/2`.
:::

:::definition "minimal_edge_bound" (parent := "threshold_bridge") (uses := "minimal_members")
For an increasing family $`\mathcal F`, let $`\ell(\mathcal F)` be the larger
of $`2` and the maximum cardinality of a minimal member of $`\mathcal F`.
:::

:::theorem "minimal_family_not_q_small" (parent := "threshold_bridge") (uses := "minimal_members_generate, expectation_threshold, minimal_edge_bound, cover_cost") (effort := "medium") (priority := "high")
If $`q>q(\mathcal F)`, then the family of minimal members of $`\mathcal F` is
$`\ell(\mathcal F)`-bounded and has $`q`-covering cost greater than $`1/2`.
:::

:::lemma_ "binomial_level_mixture" (parent := "threshold_bridge") (uses := "bernoulli_measure, uniform_level") (effort := "large") (priority := "high")
Conditional on its cardinality being $`m`, a Bernoulli random subset of $`X`
is uniform on $`L_m(X)`.
:::

:::lemma_ "binomial_concentration_bridge" (parent := "threshold_bridge") (uses := "binomial_level_mixture, level_density_monotone") (effort := "large") (priority := "high")
If an increasing family occupies more than $`2/3` of a suitable fixed-size
level, then at a universally larger Bernoulli parameter it has probability
greater than $`1/2`.
:::

:::theorem "park_pham_theorem" (parent := "threshold_bridge") (uses := "park_pham_covering_corollary, minimal_family_not_q_small, binomial_concentration_bridge, critical_threshold") (effort := "large") (priority := "high")
There is a universal constant $`K>0` such that every nontrivial increasing
family on a finite ground set satisfies
$`p_c(\mathcal F)\leq K q(\mathcal F)\log_2\ell(\mathcal F)`.
:::

:::proof "park_pham_theorem"
Choose $`q>q(\mathcal F)` and apply the covering corollary to the minimal
members.  Transfer the resulting fixed-level density estimate to Bernoulli
measure, then let $`q` decrease to the expectation threshold.
:::
