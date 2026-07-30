# Collaborative project following a blueprint

Tom, Jerry and Spike play the following game.
Tom generates a random binary code of length `n`,
which he sends to Spike along with a *secret number* `k`
between `0` and `n-1`. Spike flips exactly one bit in the code
and then sends only the modified binary code to Jerry.
Is there a pre-established strategy for Spike and Jerry
such that Jerry can determine the *secret number* `k`
solely by looking at the code sent by Spike?

Of course, you can play the role of Tom, but you can also play the roles of Spike and Jerry by testing the functions in [TomJerrySpike.lean](TomJerrySpike.lean). Do these functions *always* work as expected?

We formalize in Lean 4, using Mathlib 4, the characterization of all values of `n` for which such a strategy exists, by filling the gaps/sorries in [SolutionDraft.lean](SolutionDraft.lean), following the blueprint https://mihaiancu.github.io/Puzzle/.

For a preparation, go to [WarmUp.lean](../WarmUp.lean).
