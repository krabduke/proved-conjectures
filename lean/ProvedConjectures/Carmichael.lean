import Mathlib

/-!
# Proofs of three OEIS conjectures on Carmichael numbers (M. Coman, 2012)

* `A182132` : if 30n-7, 90n-23, 300n-79 are prime, their product is Carmichael.
* `A182088` : if 30n-29, 60n-59, 90n-89, 180n-179 are prime, their product is Carmichael.
* `A182207` : every Korselt number divisible by primes p and 2p-1 has the form
  p(2p-1)(n(2p-2)+p) with n ≥ 1.
-/

namespace ProvedConjectures.Carmichael

/-- A Carmichael number: a composite `n > 1` such that `a^(n-1) ≡ 1 (mod n)`
for every `a` coprime to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, a.Coprime n → a ^ (n - 1) ≡ 1 [MOD n]

/-- Fermat step: if `p - 1 ∣ N - 1` then `a^(N-1) ≡ 1 (mod p)` for `a` coprime to `p`. -/
lemma pow_modEq_one_of_dvd {p N a : ℕ} (hp : p.Prime) (ha : a.Coprime p)
    (h : p - 1 ∣ N - 1) : a ^ (N - 1) ≡ 1 [MOD p] := by
  obtain ⟨k, hk⟩ := h
  have hf : a ^ (p - 1) ≡ 1 [MOD p] := by
    have := Nat.ModEq.pow_totient ha
    rwa [Nat.totient_prime hp] at this
  rw [hk, pow_mul]
  simpa using hf.pow k

/-- Korselt's criterion (sufficiency), three distinct primes. -/
theorem carmichael_of_three {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (h1 : p - 1 ∣ p * q * r - 1) (h2 : q - 1 ∣ p * q * r - 1)
    (h3 : r - 1 ∣ p * q * r - 1) : IsCarmichael (p * q * r) := by
  have cpq : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  have cpr : p.Coprime r := (Nat.coprime_primes hp hr).2 hpr
  have cqr : q.Coprime r := (Nat.coprime_primes hq hr).2 hqr
  have hp2 := hp.two_le; have hq2 := hq.two_le; have hr2 := hr.two_le
  refine ⟨?_, ?_, ?_⟩
  · have : 4 ≤ p * q := Nat.mul_le_mul hp2 hq2
    nlinarith
  · intro hN
    rw [Nat.prime_mul_iff] at hN
    rcases hN with ⟨h, _⟩ | ⟨_, h⟩
    · rw [Nat.prime_mul_iff] at h; omega
    · have : 4 ≤ p * q := Nat.mul_le_mul hp2 hq2
      omega
  · intro a ha
    have dp : p ∣ p * q * r := ⟨q * r, by ring⟩
    have dq : q ∣ p * q * r := ⟨p * r, by ring⟩
    have dr : r ∣ p * q * r := ⟨p * q, by ring⟩
    have e1 := pow_modEq_one_of_dvd hp (Nat.Coprime.coprime_dvd_right dp ha) h1
    have e2 := pow_modEq_one_of_dvd hq (Nat.Coprime.coprime_dvd_right dq ha) h2
    have e3 := pow_modEq_one_of_dvd hr (Nat.Coprime.coprime_dvd_right dr ha) h3
    have e12 := (Nat.modEq_and_modEq_iff_modEq_mul cpq).1 ⟨e1, e2⟩
    exact (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_mul_iff_left.2 ⟨cpr, cqr⟩)).1 ⟨e12, e3⟩

/-- Korselt's criterion (sufficiency), four distinct primes. -/
theorem carmichael_of_four {p q r s : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hs : s.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r) (hqs : q ≠ s)
    (hrs : r ≠ s)
    (h1 : p - 1 ∣ p * q * r * s - 1) (h2 : q - 1 ∣ p * q * r * s - 1)
    (h3 : r - 1 ∣ p * q * r * s - 1) (h4 : s - 1 ∣ p * q * r * s - 1) :
    IsCarmichael (p * q * r * s) := by
  have cpq : p.Coprime q := (Nat.coprime_primes hp hq).2 hpq
  have cpr : p.Coprime r := (Nat.coprime_primes hp hr).2 hpr
  have cps : p.Coprime s := (Nat.coprime_primes hp hs).2 hps
  have cqr : q.Coprime r := (Nat.coprime_primes hq hr).2 hqr
  have cqs : q.Coprime s := (Nat.coprime_primes hq hs).2 hqs
  have crs : r.Coprime s := (Nat.coprime_primes hr hs).2 hrs
  have hp2 := hp.two_le; have hq2 := hq.two_le; have hr2 := hr.two_le; have hs2 := hs.two_le
  have h4pq : 4 ≤ p * q := Nat.mul_le_mul hp2 hq2
  have h8 : 8 ≤ p * q * r := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · intro hN
    rw [Nat.prime_mul_iff] at hN
    rcases hN with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  · intro a ha
    have dp : p ∣ p * q * r * s := ⟨q * r * s, by ring⟩
    have dq : q ∣ p * q * r * s := ⟨p * r * s, by ring⟩
    have dr : r ∣ p * q * r * s := ⟨p * q * s, by ring⟩
    have ds : s ∣ p * q * r * s := ⟨p * q * r, by ring⟩
    have e1 := pow_modEq_one_of_dvd hp (Nat.Coprime.coprime_dvd_right dp ha) h1
    have e2 := pow_modEq_one_of_dvd hq (Nat.Coprime.coprime_dvd_right dq ha) h2
    have e3 := pow_modEq_one_of_dvd hr (Nat.Coprime.coprime_dvd_right dr ha) h3
    have e4 := pow_modEq_one_of_dvd hs (Nat.Coprime.coprime_dvd_right ds ha) h4
    have e12 := (Nat.modEq_and_modEq_iff_modEq_mul cpq).1 ⟨e1, e2⟩
    have e123 := (Nat.modEq_and_modEq_iff_modEq_mul (Nat.coprime_mul_iff_left.2 ⟨cpr, cqr⟩)).1 ⟨e12, e3⟩
    exact (Nat.modEq_and_modEq_iff_modEq_mul
      (Nat.coprime_mul_iff_left.2 ⟨Nat.coprime_mul_iff_left.2 ⟨cps, cqs⟩, crs⟩)).1 ⟨e123, e4⟩

/-- Helper: if `N = d * Q + 1` then `d ∣ N - 1`. -/
lemma dvd_sub_one_of_eq {N d Q : ℕ} (h : N = d * Q + 1) : d ∣ N - 1 :=
  ⟨Q, by omega⟩

/-- **OEIS A182132** (conjecture of M. Coman, 2012). -/
theorem A182132 (n : ℕ) (hn : 1 ≤ n) (hp : (30 * n - 7).Prime) (hq : (90 * n - 23).Prime)
    (hr : (300 * n - 79).Prime) :
    IsCarmichael ((30 * n - 7) * (90 * n - 23) * (300 * n - 79)) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have e1 : 30 * (t + 1) - 7 = 30 * t + 23 := by omega
  have e2 : 90 * (t + 1) - 23 = 90 * t + 67 := by omega
  have e3 : 300 * (t + 1) - 79 = 300 * t + 221 := by omega
  rw [e1] at hp; rw [e2] at hq; rw [e3] at hr; rw [e1, e2, e3]
  apply carmichael_of_three hp hq hr (by omega) (by omega) (by omega)
  · rw [show 30 * t + 23 - 1 = 30 * t + 22 by omega]
    exact dvd_sub_one_of_eq (Q := 15480 + 40890 * t + 27000 * t ^ 2) (by ring)
  · rw [show 90 * t + 67 - 1 = 90 * t + 66 by omega]
    exact dvd_sub_one_of_eq (Q := 5160 + 13630 * t + 9000 * t ^ 2) (by ring)
  · rw [show 300 * t + 221 - 1 = 300 * t + 220 by omega]
    exact dvd_sub_one_of_eq (Q := 1548 + 4089 * t + 2700 * t ^ 2) (by ring)

/-- **OEIS A182088** (conjecture of M. Coman, 2012). -/
theorem A182088 (n : ℕ) (hn : 1 ≤ n) (hp : (30 * n - 29).Prime) (hq : (60 * n - 59).Prime)
    (hr : (90 * n - 89).Prime) (hs : (180 * n - 179).Prime) :
    IsCarmichael ((30 * n - 29) * (60 * n - 59) * (90 * n - 89) * (180 * n - 179)) := by
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 1 := ⟨n - 1, by omega⟩
  have e1 : 30 * (t + 1) - 29 = 30 * t + 1 := by omega
  have e2 : 60 * (t + 1) - 59 = 60 * t + 1 := by omega
  have e3 : 90 * (t + 1) - 89 = 90 * t + 1 := by omega
  have e4 : 180 * (t + 1) - 179 = 180 * t + 1 := by omega
  rw [e1] at hp; rw [e2] at hq; rw [e3] at hr; rw [e4] at hs; rw [e1, e2, e3, e4]
  have ht : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h | h
    · subst h; exact absurd hp (by norm_num)
    · exact h
  apply carmichael_of_four hp hq hr hs (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)
  · rw [show 30 * t + 1 - 1 = 30 * t by omega]
    exact dvd_sub_one_of_eq (Q := 12 + 1410 * t + 64800 * t ^ 2 + 972000 * t ^ 3) (by ring)
  · rw [show 60 * t + 1 - 1 = 60 * t by omega]
    exact dvd_sub_one_of_eq (Q := 6 + 705 * t + 32400 * t ^ 2 + 486000 * t ^ 3) (by ring)
  · rw [show 90 * t + 1 - 1 = 90 * t by omega]
    exact dvd_sub_one_of_eq (Q := 4 + 470 * t + 21600 * t ^ 2 + 324000 * t ^ 3) (by ring)
  · rw [show 180 * t + 1 - 1 = 180 * t by omega]
    exact dvd_sub_one_of_eq (Q := 2 + 235 * t + 10800 * t ^ 2 + 162000 * t ^ 3) (by ring)

/-- A Korselt number: squarefree, and `q - 1 ∣ C - 1` for every prime `q ∣ C`.
By Korselt's criterion (1899) the composite Korselt numbers are exactly the
Carmichael numbers. -/
def IsKorselt (C : ℕ) : Prop :=
  Squarefree C ∧ ∀ q : ℕ, q.Prime → q ∣ C → q - 1 ∣ C - 1

/-- **OEIS A182207** (conjecture of M. Coman, 2012): any Korselt number `C` divisible by
primes `p` and `2p-1` has the form `C = p(2p-1)(n(2p-2)+p)` with `n ≥ 1`. -/
theorem A182207 {C p : ℕ} (hK : IsKorselt C) (hp : p.Prime) (hq : (2 * p - 1).Prime)
    (hpC : p ∣ C) (hqC : 2 * p - 1 ∣ C) :
    ∃ n : ℕ, 1 ≤ n ∧ C = p * (2 * p - 1) * (n * (2 * p - 2) + p) := by
  obtain ⟨hsf, hkor⟩ := hK
  have hC0 : C ≠ 0 := by rintro rfl; exact not_squarefree_zero hsf
  -- p is odd: if p = 2 then 3 ∣ C gives 2 ∣ C - 1, contradicting 2 ∣ C.
  have hodd : p ≠ 2 := by
    rintro rfl
    have h := hkor 3 (by norm_num) (by simpa using hqC)
    norm_num at h
    omega
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 := by
    rcases hp.eq_two_or_odd' with h | ⟨j, hj⟩
    · exact absurd h hodd
    · exact ⟨j, hj⟩
  have hj : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · subst h; exact absurd hp (by norm_num)
    · exact h
  have e1 : 2 * (2 * j + 1) - 1 = 4 * j + 1 := by omega
  have e2 : 2 * (2 * j + 1) - 2 = 4 * j := by omega
  rw [e1] at hq hqC ⊢
  rw [e2]
  have hcop : (2 * j + 1).Coprime (4 * j + 1) := (Nat.coprime_primes hp hq).2 (by omega)
  obtain ⟨m, rfl⟩ := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpC hqC
  have hd := hkor (4 * j + 1) hq ⟨(2 * j + 1) * m, by ring⟩
  rw [show 4 * j + 1 - 1 = 4 * j by omega] at hd
  have hm0 : m ≠ 0 := by rintro rfl; simp at hC0
  -- Move to ℤ: 4j ∣ m - (2j+1).
  have hdZ : ((4 * j : ℕ) : ℤ) ∣ ((2 * j + 1) * (4 * j + 1) * m : ℕ) - 1 := by
    have h1 : 1 ≤ (2 * j + 1) * (4 * j + 1) * m := Nat.one_le_iff_ne_zero.2 hC0
    have := Int.natCast_dvd_natCast.2 hd
    rwa [Nat.cast_sub h1, Nat.cast_one] at this
  push_cast at hdZ
  have key : (4 * (j : ℤ)) ∣ (m : ℤ) - (2 * j + 1) := by
    have := dvd_mul_of_dvd_right hdZ (2 * (j : ℤ) + 1)
    have h2 : (2 * (j : ℤ) + 1) * ((2 * j + 1) * (4 * j + 1) * m - 1)
        = ((m : ℤ) - (2 * j + 1)) + 4 * j * ((j + 1) * m + (2 * j + 1) ^ 2 * m) := by ring
    rw [h2] at this
    exact (dvd_add_left (dvd_mul_right _ _)).1 this
  obtain ⟨c, hc⟩ := key
  have hm : (m : ℤ) = 4 * j * c + (2 * j + 1) := by linarith
  have hjZ : (1 : ℤ) ≤ j := by exact_mod_cast hj
  have hc0 : 0 ≤ c := by
    by_contra hneg'
    have hneg : c < 0 := lt_of_not_ge hneg'
    have : (m : ℤ) ≤ 4 * j * (-1) + (2 * j + 1) := by nlinarith
    have : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    linarith
  -- c = 0 would give p² ∣ C, contradicting squarefreeness.
  have hc1 : 1 ≤ c := by
    rcases hc0.lt_or_eq with h | h
    · omega
    · exfalso
      subst h
      have hmp : m = 2 * j + 1 := by omega
      subst hmp
      have := hsf (2 * j + 1) ⟨4 * j + 1, by ring⟩
      rw [Nat.isUnit_iff] at this
      omega
  refine ⟨c.toNat, by omega, ?_⟩
  have h3 : ((c.toNat * (4 * j) + (2 * j + 1) : ℕ) : ℤ) = m := by
    push_cast; rw [Int.toNat_of_nonneg hc0]; linarith
  have : m = c.toNat * (4 * j) + (2 * j + 1) := by exact_mod_cast h3.symm
  rw [this]

end ProvedConjectures.Carmichael
