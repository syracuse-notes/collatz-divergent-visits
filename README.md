# Divergent Collatz trajectories visit dyadic intervals sparsely

Draft paper, Lean 4 formalization, and verification scripts.

**Result.** Let T(n) = n/2 (even) or (3n+1)/2 (odd). If the T-orbit of N is not eventually periodic, then for every e ≥ 3 it enters [2^e, 2^{e+1}) at most 10·e·2^{0.9603e} times (constant independent of N). Hence Σ_t 1/T^t(N) < ∞, and T^t(N)·2^t/3^{j_t} converges to a finite positive limit (j_t = number of odd steps). **Not a new result:** up to the explicit constants, this follows from Garcia & Tal, Acta Arith. 90.3 (1999), 245–250, inequality (6); see paper §1, "Prior work". What is added here is an explicit exponent and constant, a different proof, and a Lean formalization. This does **not** prove the Collatz conjecture: it constrains, but does not exclude, divergent trajectories, and it says nothing about cycles.

- `paper.md`: statement and proof, with scope of the formalization stated explicitly.
- `lean/`: Lean 4.34.1, no Mathlib. `cd lean && lake build`. Main theorems `L5M.L5_main` (finite-horizon integer theorem) and `L5M.L5_all_time` (all times). `#print axioms` gives propext, Classical.choice, Quot.sound; no `sorry`.
- `scripts/`: finite numerical checks (not part of the proof).

## Not formalized

The final parameter choice and logarithmic estimate (paper §5.2), the equivalence "not eventually periodic ⇔ injective orbit", and the corollaries are proved by hand.

## AI disclosure

- **Author.** The account owner is not a mathematician. They directed the project but did not independently verify the mathematics.
- **Mathematics, Lean code and paper text.** Produced by Claude (Anthropic): mainly Claude Opus 5.5, with parts of the exploration done by Claude Fable 5.1.
- **Adversarial reviews.** Two rounds by ChatGPT (OpenAI; GPT-6 Astra and GPT-5.6 Sol). The second round recompiled the Lean code. All points raised were addressed in v2.
- **Status.** No human mathematician has reviewed this work yet.
