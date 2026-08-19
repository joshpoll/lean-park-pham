import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import ParkPham.Chapters.Foundations
import ParkPham.Chapters.FiniteCombinatorics
import ParkPham.Chapters.Covering
import ParkPham.Chapters.Threshold

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The Park–Pham Theorem" =>

This is a working blueprint for a Lean formalization of the expectation-threshold
theorem.  The central route follows Tran and Vu's short inductive proof of the
Park–Pham covering theorem.  The final chapter then connects that finite
covering statement to Bernoulli thresholds.

The graph deliberately contains results that have not yet been stated in Lean.
As declarations and proofs are attached to their labels, their status will be
computed from the Lean code.

{include 0 ParkPham.Chapters.Foundations}
{include 0 ParkPham.Chapters.FiniteCombinatorics}
{include 0 ParkPham.Chapters.Covering}
{include 0 ParkPham.Chapters.Threshold}

{blueprint_graph (direction := BT) (preview := pinned)}
{blueprint_summary}
