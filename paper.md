# Divergent Collatz trajectories visit dyadic intervals sparsely

*Draft v2, 2026-09-28. Revised after two adversarial reviews. Not peer-reviewed.*

*Formalization scope:* Lean 4 (no Mathlib) checks the finite-horizon integer counting theorem that underlies Theorem 1 (`L5M.L5_main`). It also checks the passage from every finite horizon to all times (`L5M.L5_all_time`). The choice of parameters and the logarithmic estimate in §5.2 are proved by hand. So are the corollaries in §1.

## Abstract

Let T(n) = n/2 for even n and (3n+1)/2 for odd n. Suppose the T-orbit of N is not eventually periodic. We show that, for every e ≥ 3, the orbit enters [2^e, 2^{e+1}) at most 10·e·2^{0.9603e} times. The constant does not depend on N.

It follows that the reciprocals of all terms of such an orbit have a finite sum. Consequently T^t(N)·2^t/3^{j_t} → K ∈ (0, ∞), where j_t is the number of odd steps among the first t steps. The closest earlier statement we found is Lagarias (1985, eq. (2.32)), which bounds only the orbit points that are never undercut later.

## 1. Statement

Write x_t = T^t(N) and A_t = 3^{j_t}/2^t, and define c_t(N) by x_t = A_t(N + c_t(N)). For odd x, T(x) = (3/2)x(1 + 1/(3x)), so

    N + c_t(N) = N · ∏_{s<t, x_s odd} (1 + 1/(3x_s)).                (1)

For positive integers, "not eventually periodic" is equivalent to x_t → ∞. If the orbit returned infinitely often to a finite set, some value would repeat, and from then on the orbit would be periodic. It is also equivalent to t ↦ x_t being injective.

**Theorem 1.** Let N ≥ 1 have a T-orbit that is not eventually periodic. Then for every e ≥ 3,

    #{ t ≥ 0 : 2^e ≤ x_t < 2^{e+1} } ≤ 10 · e · 2^{0.9603 e}.

**Corollary 2.** For such N:
1. Σ_{t≥0} 1/x_t < ∞.
2. c_∞(N) := lim c_t(N) < ∞.
3. A_t → ∞, and x_t/A_t → K := N + c_∞(N) ∈ (0, ∞).

*Proof of Corollary 2.*
1. The values 1 ≤ x < 8 are taken at most 7 times, because the orbit is injective. By Theorem 1, the remaining terms contribute at most Σ_{e≥3} 10e·2^{0.9603e}/2^e < ∞.
2. Since Σ 1/x_t < ∞, the product in (1) converges.
3. We have N + c_t → K and x_t → ∞, so A_t = x_t/(N + c_t) → ∞. ∎

In words: a divergent trajectory, if one exists, cannot diverge more slowly than its multiplier 3^{j_t}/2^t. Theorem 1 does not exclude divergent trajectories. It constrains their structure.

**Comparison.** Lagarias (Amer. Math. Monthly 92 (1985), eq. (2.32), from Theorem F) shows the following. Let U_D be the set of points n of the orbit with T^k(n) > n for all k ≥ 1. Then #{n ∈ U_D : n ≤ x} ≤ c·x^{1−η}, with η ≈ 0.05004. Theorem 1 bounds all orbit points instead. The new ingredient is Lemma 3: every revisit to an interval consumes a distinct rare up-crossing.

We searched Lagarias' annotated bibliographies I–II (arXiv math/0309224, math/0608208), Tao (2019), Krasikov–Lagarias (2003), and the web. We did not find Theorem 1 or Corollary 2. This is not a complete survey, so novelty is not claimed.

## 2. A combinatorial lemma for arbitrary sequences

Let x: ℕ → ℕ be any sequence, and fix Yp ≤ Y ≤ W and k, k'. Define:
- **visit(t):** Y ≤ x_t < W.
- **stay(t):** x_{t+s} ≥ Yp for all s ≤ k.
- **up-crossing at t > 0:** x_{t−1} < Yp ≤ x_t.
- **rare(t):** either
  - **(Stay′)** x_{t+s} ≥ Yp for all s ≤ k′, or
  - **(Climb)** there is s ≤ k′ with x_{t+s} ≥ Y and x_{t+r} ≥ Yp for all r ≤ s.

**Lemma 3.** For every L,

    #{t < L : visit} ≤ #{t < L : visit ∧ stay} + k · (#{t < L : rare up-crossing} + 1).

*Proof.* Cut time at the up-crossings into epochs. Within an epoch starting at p, every visit t satisfies x_r ≥ Yp for all p ≤ r ≤ t. Otherwise the last value below Yp before t would be followed by an up-crossing inside the epoch.

(a) An epoch that starts with a non-rare up-crossing contains no visit. A visit at t would make the start rare: take s = t − p for Climb if t − p ≤ k′, and use Stay′ otherwise.

(b) The non-staying visits of an epoch lie in [t₀, t₀ + k), where t₀ is the first of them. The value at t₀ drops below Yp within k steps, and no later visit of the same epoch can come after that drop.

The "+1" accounts for the initial epoch. ∎ (Lean: `L5.L5_comb`.)

## 3. Counting in arithmetic progressions

Let oddCnt_k(x) be the number of odd steps among the first k steps from x. Take a progression a + d·i (0 ≤ i < 2^k·m) with d odd. Its even terms are mapped by T onto a progression with difference d, and its odd terms onto one with difference 3d. This gives an induction on k.

**Lemma 4.** For u ≥ w and all t,

    #{i : t ≤ oddCnt_k(a+di)} · u^t w^k ≤ m (u+w)^k w^t.

(Lean: `L5C.chernoff`.)

**Lemma 5.** For all num and den,

    #{i : ∃ s ≤ k, den·2^s ≤ num·3^{oddCnt_s(a+di)}} · den ≤ m·2^k·num.

(Lean: `L5C.doob`. This is the optional-stopping bound for the martingale 3^j/2^s, whose one-step mean is 1.)

## 4. The correction term

**Lemma 6.** Suppose every odd value among the first s steps from x is at least n ≥ 1, and 2·oddCnt_s(x) ≤ 3n + 1. Then

    2^s·T^s(x) ≤ 2·3^{oddCnt_s(x)}·x.

(Lean: `L5L.correction`.)

## 5. Proof of Theorem 1

### 5.1 The integer theorem (formalized)

Suppose t ↦ x_t is injective, and the integers Yp, Y, k, k′, u, w, t₀, t₁, m₁, m₂ satisfy:

- (H1) 1 ≤ Yp ≤ Y and w ≤ u;
- (H2) 2k ≤ 3Yp + 1 and 2k′ ≤ 3Yp + 1;
- (H3) Y ≤ 2^k·m₁ and ⌊Yp/2⌋ + 1 ≤ 2^{k′}·m₂;
- (H4) for all j, Yp·2^k ≤ 4Y·3^j ⇒ t₀ ≤ j;
- (H5) for all j, Yp·2^{k′} ≤ 3Yp·3^j ⇒ t₁ ≤ j.

Then for every L,

    #{t < L : Y ≤ x_t < 2Y} ≤ S + k(C + P + 1),

where S, C, P are integers that do not depend on N or L, and

    S·u^{t₀}w^k ≤ m₁(u+w)^k w^{t₀},   C·Y ≤ m₂·2^{k′}·3Yp,   P·u^{t₁}w^{k′} ≤ m₂(u+w)^{k′}w^{t₁}.

(Lean: `L5M.L5_main`, with S, C, P given by the explicit definitions `Sb`, `Cb`, `Pb`.)

*Sketch.* Apply Lemma 3 with W = 2Y. The orbit is injective, so a count over times is at most the count over values (pigeonhole, `L5.pigeon`).

- A staying visit v ∈ [Y, 2Y) satisfies Yp·2^k ≤ 2·3^j·v ≤ 4Y·3^j by Lemma 6. So j ≥ t₀, and Lemma 4 applies.
- An up-crossing value z satisfies Yp ≤ z and 2z + 2 ≤ 3Yp, because the previous value is odd and below Yp.
  - Stay′ gives Yp·2^{k′} ≤ 3Yp·3^j, handled by Lemma 4.
  - Climb gives Y·2^s ≤ 3Yp·3^{oddCnt_s(z)}, handled by Lemma 5.

**From finite L to all times** (Lean: `L5M.L5_all_time`). The bound B = S + k(C + P + 1) does not depend on L. The count V_L is nondecreasing in L and integer-valued, so it is eventually constant. Hence there is an L₀ with no visits at times t ≥ L₀, and the total number of visits is V_{L₀} ≤ B.

### 5.2 Parameters and the exponent (by hand)

Let e ≥ 3, and put e′ = e − ⌈e/50⌉. Then 0.98e − 1 < e′ ≤ 0.98e and e′ ≥ 2. Set:

    Y = 2^e,  Yp = 2^{e′},  k = e,  m₁ = 1,  k′ = e′ − 1,  m₂ = 2,  (u, w) = (3, 2),
    t₀ = min{ j ≥ 0 : 3^j ≥ 2^{e′−2} },
    t₁ = min{ j ≥ 0 : 3^{j+1} ≥ 2^{k′} }.

*Checking the hypotheses.*
- (H1): immediate.
- (H2): e′ ≥ max(2, 0.98e − 1) gives 3·2^{e′} ≥ 2e for all e ≥ 3, and k′ < k.
- (H3): 2^e ≤ 2^e·1, and 2^{e′−1} + 1 ≤ 2^{e′−1}·2 because e′ ≥ 1.
- (H4): Yp·2^k ≤ 4Y·3^j is equivalent to 2^{e′−2} ≤ 3^j, so t₀ ≤ j by minimality.
- (H5): Yp·2^{k′} ≤ 3Yp·3^j is equivalent to 2^{k′} ≤ 3^{j+1}, so t₁ ≤ j by minimality.
- Injectivity holds because the orbit is not eventually periodic.

*Estimates.* Write λ = log₂3, a = log₂(5/2) = 1.3219281…, and β = log₂(3/2) = 0.5849625…. By minimality, t₀ ≥ (e′ − 2)/λ and t₁ ≥ k′/λ − 1.

- **S.** Since m₁ = 1, S ≤ (5/2)^e (2/3)^{t₀}. So
  log₂S ≤ ae − (e′ − 2)β/λ < ae − (0.98e − 3)β/λ = (a − 0.98β/λ)e + 3β/λ.
  Here a − 0.98β/λ = 0.9602393… and 3β/λ = 1.1072…. Hence S ≤ 2^{1.108}·2^{0.96024e}.
- **C.** C ≤ 2·2^{e′−1}·3·2^{e′}/2^e = 3·2^{2e′−e} ≤ 3·2^{0.96e}.
- **P.** P ≤ 2(5/2)^{k′}(2/3)^{t₁}. So
  log₂P ≤ 1 + (a − β/λ)k′ + β = 0.9528578…k′ + 1.585. Since k′ < 0.98e, this is at most 0.9338e + 1.585, and P ≤ 3·2^{0.9338e}.

Therefore, for every e ≥ 3,

    V ≤ S + e(C + P + 1) ≤ (2.16 + 3e + 3e + e)·2^{0.96024e} ≤ 10·e·2^{0.9603e}.

This completes the proof of Theorem 1. ∎

*Supplementary check (not part of the proof).* We evaluated the exact integer bound S + k(C + P + 1) for every e = 3, …, 3000; it is below 10·e·2^{0.9603e} in all cases (`scripts/verify_parameters.py`).

## 6. Formalization

Lean 4.34.1, no Mathlib. The files are `lean/L5Comb.lean`, `L5Count.lean`, `L5Link.lean`, `L5Pigeon.lean` and `L5Main.lean`, built with `lake build`. For both `L5M.L5_main` and `L5M.L5_all_time`, `#print axioms` reports propext, Classical.choice and Quot.sound. There are no `sorry`s.

**Formalized:** Lemmas 3–6, the pigeonhole step, the integer theorem of §5.1, and the passage from finite L to all times.

**Not formalized:**
- the equivalence between "not eventually periodic" and injectivity (§1);
- the parameter choice and the logarithmic estimate (§5.2);
- Corollary 2.

## 7. Limitations

Theorem 1 does not rule out divergent trajectories. It shows that any such trajectory satisfies x_t·2^t/3^{j_t} → K ∈ (0, ∞).

Theorem 1 also says nothing about non-trivial cycles; it assumes the orbit is not eventually periodic. (For a periodic orbit, Σ_t 1/x_t = ∞.)

Ruling out divergent trajectories would additionally require excluding orbits with A_t → ∞. The counting arguments used here do not reach that case: a single-scale counting argument cannot exclude an orbit that crosses each scale only a bounded number of times.
