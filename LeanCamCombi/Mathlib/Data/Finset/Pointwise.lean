import Mathlib.Data.Finset.Pointwise

open MulOpposite
open scoped Pointwise

variable {α : Type*}

namespace Finset
section Mul
variable [DecidableEq α] [Mul α]

@[to_additive (attr := simp)]
lemma singleton_mul' (a : α) (s : Finset α) : {a} * s = a • s := singleton_mul _

@[to_additive (attr := simp)]
lemma mul_singleton' (s : Finset α) (a : α) : s * {a} = op a • s := mul_singleton _

end Mul
end Finset
