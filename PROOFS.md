# Proofs of three OEIS conjectures on Carmichael numbers (Coman, 2012)

All three rely on **Korselt's criterion**: a composite N is a Carmichael number iff N is
squarefree and (q − 1) | (N − 1) for every prime q | N.

Status at time of writing (Nov 2026): all three entries still say "Conjecture", with no proof
recorded in OEIS. Numerical checks: `scripts/check_carmichael.py`. Machine-checked proofs:
`lean/ProvedConjectures/Carmichael.lean` (including both directions of Korselt's criterion).

---

## A182132 — C = (30n−7)(90n−23)(300n−79)

**Claim.** If 30n−7, 90n−23, 300n−79 are all prime, then C is a Carmichael number.

**Proof.** Put m = 15n − 4. Then the factors are 2m+1, 6m+1, 20m+1, and

C − 1 = (2m+1)(6m+1)(20m+1) − 1 = m(28 + 172m + 240m²).

It suffices to show 20m | C−1 and 6m | C−1 (then 2m | C−1 too), i.e.
20 | 28 + 172m + 240m² and 6 | 28 + 172m + 240m².

- mod 4: 28 + 172m + 240m² ≡ 0. ✓
- mod 5: ≡ 3 + 2m. Since m = 15n − 4 ≡ 1 (mod 5), this is 5 ≡ 0. ✓
- mod 2: ≡ 0. ✓
- mod 3: ≡ 1 + m. Since m ≡ 2 (mod 3), this is 3 ≡ 0. ✓

The three primes are distinct, so C is squarefree and composite. By Korselt, C is Carmichael. ∎

(In fact the divisibilities hold for **every** n ≥ 1; primality is only needed for Korselt.)

---

## A182088 — C = (30n−29)(60n−59)(90n−89)(180n−179)

**Claim.** If all four factors are prime, C is a Carmichael number.

**Proof.** Put k = 30(n−1). The factors are k+1, 2k+1, 3k+1, 6k+1 (n ≥ 2 so k > 0), and

C − 1 = k(12 + 47k + 72k² + 36k³).

Each q − 1 ∈ {k, 2k, 3k, 6k} divides 6k, so it suffices that 6 | 12 + 47k + 72k² + 36k³,
i.e. 6 | 47k. True since 6 | k. The four primes are distinct, so Korselt applies. ∎

---

## A182207 — C = p(2p−1)(n(2p−2) + p)

**Claim.** Every Carmichael number C divisible by p and 2p−1 (both prime) has the form
C = p(2p−1)(n(2p−2) + p) for some integer n ≥ 1.

**Proof.** Carmichael numbers are odd, so p is odd (p ≥ 3). Write C = p(2p−1)m.
Since 2p−1 is a prime factor of C, Korselt gives (2p−2) | (C−1), i.e.

p(2p−1)m ≡ 1 (mod 2p−2).

Now 2p−1 ≡ 1 (mod 2p−2), so p·m ≡ 1. Also p² − 1 = (p−1)(p+1), and p+1 is even, so
2(p−1) | p² − 1, i.e. p² ≡ 1 (mod 2p−2). Multiplying p·m ≡ 1 by p gives m ≡ p (mod 2p−2).

Since 0 < p < 2p−2 and m > 0, m = p + n(2p−2) with n ≥ 0. If n = 0 then p² | C,
contradicting squarefreeness. So n ≥ 1. ∎
