/-
Copyright (c) 2023 Yves Jäckle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Yves Jäckle.
-/
import LeanCamCombi.Mathlib.Data.Nat.GCD.Basic
import LeanCamCombi.Mathlib.NumberTheory.Fermat

/-!
# Six proofs of the inﬁnity of primes : 2nd proof

This file is part of a Master thesis project of formalizing some proofs from
"Proofs from THE BOOK" (5th ed.) by Martin Aigner and Günter M. Ziegler.

We refer to chapter 1: "Six proofs of the inﬁnity of primes".
In this file, we formalize the "Second proof",
which makes use of Fermat numbers.

This proof is based on the formalization of Moritz Firsching,
whose orginial work can be found on the repository at:
https://github.com/eric-wieser/formal_book

We've made some modifications and additions.

## Structure

- `second_proof`:
      The conclusion of our work. We show that we can form
      a (infinite) sequence of primes all pairwise different.
- `second_proof_standardised` :
      Infinitude of primes in terms of `set.infinite`,
      proven with `second_proof`.
- `F` :
      denotes  the Fermat number sequence.
- `fermatNumber_product` :
      the recurrence relation satisfied by the Fermat numbers.
- `coprime_fermatNumber_fermatNumbers` :
      We show that the Fermat numbers are pairwise coprime.
      This is the the key step in showing infinitude of primes,
      as these numbers must have prime divisors, which must be
      pairwise different due to dividing coprime numbers.
-/

-- TODO: Protect `Nat.pow_succ`/`Nat.pow_succ'`, `Nat.ne_of_gt`

open Finset Function Nat
open scoped BigOperators

/-- ### 2nd proof of the infinitude of primes

Consider a sequence of prime divisors of the *Fermat numbers*,
one divisor per Fermat number.

These primes must be different: if the divisors were equal,
they would divide the coprime Fermat numbers, and yet, be prime,
which is impossible.
-/
lemma second_proof : ∃ P : ℕ → ℕ, Injective P ∧ ∀ k, (P k).Prime := by
  -- the primes are different
  -- We consider some list of prime divisors of the fermatNumber numbers
  choose P hprime hdvd using fun n ↦ exists_prime_and_dvd (fermatNumber_ne_one n)
  -- These prime divisors must all be different
  refine ⟨P, fun m n hmn ↦ ?_, hprime⟩
  · -- If the divisors were equal, they would divide coprime numbers,
    -- and yet, be prime, which is impossible.
    refine pairwise_coprime_fermatNumber.eq fun h ↦ ?_
    simpa [hmn, (hprime _).ne_one] using h.of_dvd (hdvd _) (hdvd _)

-- watch out for the simple `prime.ne_one`
-- that won't recognize primes in naturals.
/-- The standardised statement proven through Euclids proof-/
lemma second_proof_standardised : {n : ℕ | n.Prime}.Infinite := by
  obtain ⟨P, hinj, hprime⟩ := second_proof
  exact Set.infinite_of_injective_forall_mem hinj hprime
