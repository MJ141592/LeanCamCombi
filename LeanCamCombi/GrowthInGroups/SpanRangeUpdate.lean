import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Ideal.Span

open Polynomial

variable {R ι : Type*} [CommRing R] [DecidableEq ι]

lemma Ideal.span_range_update_divByMonic (v : ι → R[X]) {i j : ι} (hij : i ≠ j) (H : (v i).Monic) :
    span (Set.range (Function.update v j (v j %ₘ v i))) = span (Set.range v) := by
  refine le_antisymm ?_ ?_ <;> simp only [span_le, Set.range_subset_iff, SetLike.mem_coe] <;>
    intro k <;> obtain rfl | hjk := eq_or_ne j k
  · rw [Function.update_same, modByMonic_eq_sub_mul_div (v j) H]
    exact sub_mem (subset_span ⟨j, rfl⟩) <| mul_mem_right _ _ <| subset_span ⟨i, rfl⟩
  · exact subset_span ⟨k, (Function.update_noteq (.symm hjk) _ _).symm⟩
  · nth_rw 2 [← modByMonic_add_div (v j) H]
    apply add_mem (subset_span ?_) (mul_mem_right _ _ (subset_span ?_))
    · exact ⟨j, Function.update_same _ _ _⟩
    · exact ⟨i, Function.update_noteq hij _ _⟩
  · exact subset_span ⟨k, Function.update_noteq (.symm hjk) _ _⟩
