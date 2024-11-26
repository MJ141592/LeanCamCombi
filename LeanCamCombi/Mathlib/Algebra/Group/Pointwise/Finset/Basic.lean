import Mathlib.Algebra.Group.Pointwise.Finset.Basic

open scoped Pointwise

namespace Finset
variable {α : Type*} [DecidableEq α]

section Mul
variable [Mul α] {s t : Finset α} {a : α}

@[to_additive]
lemma smul_finset_subset_mul : a ∈ s → a • t ⊆ s * t := image_subset_image₂_right

attribute [gcongr] div_subset_div_left div_subset_div_right

end Mul

section Monoid
variable [Monoid α] {s t : Finset α} {a : α} {n : ℕ}

@[to_additive]
lemma subset_pow (hs : 1 ∈ s) (hn : n ≠ 0) : s ⊆ s ^ n := by
  simpa using pow_subset_pow_right hs <| Nat.one_le_iff_ne_zero.2 hn

end Monoid

section CancelMonoid
variable [CancelMonoid α] {s t : Finset α} {a : α} {n : ℕ}

@[to_additive]
lemma Nontrivial.mul_right : s.Nontrivial → t.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨a * c, mul_mem_mul ha hc, b * c, mul_mem_mul hb hc, by simpa⟩

@[to_additive]
lemma Nontrivial.mul_left : t.Nontrivial → s.Nonempty → (s * t).Nontrivial := by
  rintro ⟨a, ha, b, hb, hab⟩ ⟨c, hc⟩
  exact ⟨c * a, mul_mem_mul hc ha, c * b, mul_mem_mul hc hb, by simpa⟩

@[to_additive]
lemma Nontrivial.mul (hs : s.Nontrivial) (ht : t.Nontrivial) : (s * t).Nontrivial :=
  hs.mul_right ht.nonempty

@[to_additive]
lemma Nontrivial.pow (hs : s.Nontrivial) : ∀ {n}, n ≠ 0 → (s ^ n).Nontrivial
  | 1, _ => by simpa
  | n + 2, _ => by simpa [pow_succ] using (hs.pow n.succ_ne_zero).mul hs

end CancelMonoid
end Finset
