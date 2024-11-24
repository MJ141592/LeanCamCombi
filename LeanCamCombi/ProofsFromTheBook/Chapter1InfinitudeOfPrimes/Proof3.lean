/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import Mathlib.FieldTheory.Finite.Basic

/-!
# Six proofs of the inﬁnity of primes : 3rd proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize the "Third proof",
which makes use of Mersenne numbers.

## Structure

- `third_proof`:
      We show that there are infinitely many primes, in the sense that
      for any finite set, there is a prime not contained in it.

- `third_proof_standardised` :
      Infinitude of primes in terms of `set.infinite`,
      proven with `third_proof`.

-/


open Nat Finset

/-- ### 3rd proof of the infinitude of primes

Assume that there are finitely many primes and
consider their largest one `p`. Next, consider a prime
divisor `q` of the *Mersenne number* `2^p - 1`.

- In ℤ/qℤ, the order of 2 divides p and is therefore p
- Also, the order of 2 divides q-1 by Fermat's little theorem

Hence, `p < q`, which contradicts maximality of p,
as q is also a prime.

-/
theorem third_proof (s : Finset ℕ) : ∃ p, Nat.Prime p ∧ p ∉ s := by
  by_contra! h
  set s_primes := s.filter Nat.Prime with s_primes_def
  -- Let's add a membership definition lemma to ease exposition, as in the first proof
  have mem_s_primes : ∀ {n : ℕ}, n ∈ s_primes ↔ n.Prime := by
    intro n
    rw [s_primes_def, mem_filter, and_iff_right_iff_imp]
    exact h n
  -- A tecnical requirement to define the largest element of s_primes
  have s_primes_nonempty : s_primes.Nonempty := by
    use 2
    rw [mem_s_primes]
    exact prime_two
  -- We consider the largest prime
  set p := Finset.max' s_primes s_primes_nonempty with pdef
  have p_prime : p.Prime := by
    rw [← mem_s_primes]
    rw [pdef]
    exact max'_mem s_primes s_primes_nonempty
  -- Next, we consider a prime divisor of the Mersenne number 2^p -1
  have dvd_Mers : ∃ q : ℕ, q.Prime ∧ q ∣ 2 ^ p - 1 := by
    apply exists_prime_and_dvd
    intro con
    rw [Nat.sub_eq_iff_eq_add Nat.one_le_two_pow] at con
    norm_num at con
    nth_rw 2 [← pow_one 2] at con
    exact p_prime.ne_one $ Nat.pow_right_injective le_rfl con
  rcases dvd_Mers with ⟨q, q_prime, qd2p⟩
  -- Now, we switch to the finite field ℤ/qℤ
  rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at qd2p
  -- A technical lemma needed to show `odq`.
  have q_tec : q ≠ 2 := by
    intro con
    rw [con] at qd2p
    -- click on ↑ in the infoview to see the difference
    rw [ZMod.eq_zero_iff_even] at qd2p
    rw [even_sub Nat.one_le_two_pow] at qd2p
    simp only [Nat.not_even_one, iff_false] at qd2p
    rw [even_pow] at qd2p
    exact qd2p ⟨even_two, Nat.Prime.ne_zero p_prime⟩
  -- We may then use group theory to get:
  have odq : orderOf (2 : ZMod q) ∣ q - 1 := by
    haveI : Fact (Nat.Prime q) := Fact.mk q_prime
    --this has been improved in lean 4
    -- This is the name and variant of Fermat's little theorem (as a consequence of Lagranges theorem):
    apply ZMod.orderOf_dvd_card_sub_one
    -- required the instance
    apply Ring.two_ne_zero
    rw [ZMod.ringChar_zmod_n]
    exact q_tec
  clear q_tec
  simp at qd2p
  -- Note: check simp in messages. Replacing simp with the message
  -- will fail, even if the library of the commands used is imported.
  rw [sub_eq_zero] at qd2p
  -- We use some more group theory to get:
  have odp : orderOf (2 : ZMod q) ∣ p := orderOf_dvd_of_pow_eq_one qd2p
  clear qd2p
  -- Since the order of 2 divides a prime, we have:
  rw [dvd_prime p_prime] at odp
  obtain odp | odp := odp
  -- Recall that q is a prime, and we showed it was different then 2,
  -- so that this case for `odp` is false, though we show it differently.
  · rw [orderOf_eq_iff (show 0 < 1 from zero_lt_one)] at odp
    have error_1 : (2 : ZMod q) = 1 := by rw [← pow_one (2 : ZMod q)]; exact odp.1
    have error_2 : (2 : ZMod q) ≠ 1 := by
      haveI : Fact (Nat.Prime q) := Fact.mk q_prime
      -- allows us to recall that `zmod q` is a group
      -- so that we may use `sub_eq_zero`.
      intro h
      rw [← sub_eq_zero] at h
      -- else, norm_num fails
      norm_num at h
    exact error_2 error_1
  -- Note: direct applications of norm_num, possibly with rw ← sub_eq_zero and one_ne_zero are cumbersome too
  rw [odp] at odq
  -- A consequence on the sizes:
  have dvd_bound_pre : p ≤ q - 1 := le_of_dvd (tsub_pos_of_lt q_prime.one_lt) odq
  have dvd_bound : p < q := dvd_bound_pre.trans_lt $ tsub_lt_self q_prime.pos zero_lt_one
  -- Unfortunately, there is no `nat.prime.one_le`
  clear dvd_bound_pre
  rw [pdef] at dvd_bound
  -- Yet, q is in the set `s_primes` and should be smaller then its maximum
  have problem : q ≤ s_primes.max' s_primes_nonempty := le_max' _ _ $ mem_s_primes.2 q_prime
  -- We've reach our desired contradiction:
  exact (not_le_of_lt dvd_bound) problem

--linarith,
-- alternative to the previous line
-- #check third_proof
/-- The standardised statement proven through Euclids proof-/
theorem third_proof_standardised : {n : ℕ | n.Prime}.Infinite := by
  rw [Set.Infinite]
  intro con
  obtain ⟨p, ⟨p_prop, p_mem⟩⟩ := third_proof (Set.Finite.toFinset con)
  apply p_mem
  rw [con.mem_toFinset]
  rw [Set.mem_setOf_eq]
  exact p_prop
