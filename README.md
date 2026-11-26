# Proved Conjectures

[![CI](https://github.com/krabduke/proved-conjectures/actions/workflows/ci.yml/badge.svg)](https://github.com/krabduke/proved-conjectures/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/License-MIT-blue.svg)](LICENSE)
[![Lean 4](https://img.shields.io/badge/Lean-4-informational)](https://lean-lang.org)

Proofs of previously open (if modest) conjectures from the
[On-Line Encyclopedia of Integer Sequences](https://oeis.org), each with a human-readable
proof, an independent numerical check, and a machine-checked proof in
[Lean 4](https://lean-lang.org) / [Mathlib](https://github.com/leanprover-community/mathlib4).

## Results

| OEIS | Conjecture (M. Coman, Apr 2012) | Proof | Lean |
|---|---|---|---|
| [A182132](https://oeis.org/A182132) | If 30n−7, 90n−23 and 300n−79 are all prime, their product is a Carmichael number. | ✅ | ✅ full |
| [A182088](https://oeis.org/A182088) | If 30n−29, 60n−59, 90n−89 and 180n−179 are all prime, their product is a Carmichael number. | ✅ | ✅ full |
| [A182207](https://oeis.org/A182207) | Every Carmichael number divisible by primes p and 2p−1 has the form p(2p−1)(n(2p−2)+p) with n ≥ 1. | ✅ | ✅ full |

As of November 2026 all three were still recorded in the OEIS as conjectures, checked only
for small parameters. Sibling entries by the same author (A182085, A182133, A182416) had
already been annotated "follows from Korselt's criterion"; these three had not. A web search
found no prior written proof.

### Proof sketches

A **Carmichael number** is a composite n with aⁿ⁻¹ ≡ 1 (mod n) for every a coprime to n.
**Korselt's criterion** (1899): a composite n is Carmichael iff n is squarefree and
p − 1 | n − 1 for every prime p | n.

- **A182132.** Substitute m = 15n − 4. The factors become 2m+1, 6m+1, 20m+1 and
  C − 1 = m(28 + 172m + 240m²). Korselt's conditions reduce to m ≡ 1 (mod 5) and
  m ≡ 2 (mod 3), both of which hold identically.
- **A182088.** Substitute k = 30(n − 1). The factors become k+1, 2k+1, 3k+1, 6k+1 and
  C − 1 = k(12 + 47k + 72k² + 36k³); every condition reduces to 6 | k.
- **A182207.** Write C = p(2p−1)m. Korselt for the prime 2p−1 gives p·m ≡ 1 (mod 2p−2).
  Since p² ≡ 1 (mod 2p−2), it follows that m ≡ p (mod 2p−2). Squarefreeness excludes m = p.

Full proofs: [`PROOFS.md`](PROOFS.md).

## Formal verification

Source: [`lean/ProvedConjectures/Carmichael.lean`](lean/ProvedConjectures/Carmichael.lean)

```lean
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]

theorem A182132 (n : ℕ) (hn : 1 ≤ n) (hp : (30 * n - 7).Prime) (hq : (90 * n - 23).Prime)
    (hr : (300 * n - 79).Prime) :
    IsCarmichael ((30 * n - 7) * (90 * n - 23) * (300 * n - 79))

theorem A182088 (n : ℕ) (hn : 1 ≤ n) (hp : (30 * n - 29).Prime) (hq : (60 * n - 59).Prime)
    (hr : (90 * n - 89).Prime) (hs : (180 * n - 179).Prime) :
    IsCarmichael ((30 * n - 29) * (60 * n - 59) * (90 * n - 89) * (180 * n - 179))

theorem A182207 {C p : ℕ} (hC : IsCarmichael C) (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (hpC : p ∣ C) (hqC : 2 * p - 1 ∣ C) :
    ∃ n : ℕ, 1 ≤ n ∧ C = p * (2 * p - 1) * (n * (2 * p - 2) + p)
```

### Scope of the formal verification

All three theorems are stated against the definition of a Carmichael number itself
(`IsCarmichael` above), not against Korselt's criterion. Both directions of Korselt's
criterion that the proofs need are proved in the file from Mathlib primitives:

- **Sufficiency** (used for A182132, A182088): `carmichael_of_three`, `carmichael_of_four`,
  via Fermat's little theorem and the Chinese remainder theorem.
- **Necessity** (used for A182207): `IsCarmichael.isKorselt`. Squarefreeness via
  (1 + C/p)^(C−1) ≡ 1 + (C−1)·C/p (mod C); the condition p − 1 | C − 1 via a primitive
  root mod p lifted by the Chinese remainder theorem.

- `lean/Check.lean` runs `#print axioms`; every theorem depends only on Lean's standard
  axioms `propext`, `Classical.choice` and `Quot.sound`. No `sorry`. CI fails if this
  changes.

### Building

Requires [elan](https://github.com/leanprover/elan).

```sh
cd lean
lake exe cache get          # download prebuilt Mathlib (~8 GB)
lake build
lake env lean Check.lean    # print axioms
```

## Numerical checks

```sh
python3 scripts/check_carmichael.py
```

| Conjecture | Range | Cases | Failures |
|---|---|---|---|
| A182132 | n < 300 000 | 3 947 | 0 |
| A182088 | n < 300 000 | 589 | 0 |
| A182207 | all Carmichael C < 3·10⁶ | 29 | 0 |

## Methodology

1. All ~24 000 OEIS entries containing the word "Conjecture" were extracted from the
   [official OEIS data](https://github.com/oeis/oeisdata) (`scripts/extract.py`).
2. Entries were filtered for conjectures whose recorded verification bound was small.
3. Candidates were tested numerically, then proved by hand and formalised in Lean.
4. Each candidate was checked for an existing proof in the OEIS entry and on the web.

## Repository layout

```
PROOFS.md                         human-readable proofs
lean/ProvedConjectures/           Lean 4 sources
lean/Check.lean                   axiom audit
scripts/check_carmichael.py       numerical verification
scripts/extract.py                OEIS conjecture extraction
.github/workflows/ci.yml          builds the Lean proofs and runs the numerical checks
```

## Future work

- Submit the proofs to the OEIS entries.
- Extend to further OEIS and literature conjectures.

## Credits and disclosure

Conjectures by Marius Coman (OEIS, 2012). The search, proofs and Lean formalisation were
produced with substantial AI assistance (Claude Opus 5.5, Anthropic). The results are
small: these conjectures were open because no one had written the argument down, not
because they are deep.

## License

Code and text in this repository: [MIT](LICENSE). OEIS data is © The OEIS Foundation and
licensed under [CC BY-SA 4.0](https://oeis.org/LICENSE); it is not redistributed here.
