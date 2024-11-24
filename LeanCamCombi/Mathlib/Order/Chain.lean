import Mathlib.Order.Chain

open Set

variable {α β : Type*}

theorem isChain_singleton (r : α → α → Prop) (a : α) : IsChain r {a} :=
  pairwise_singleton _ _

theorem isChain_pair (r : α → α → Prop) {a b : α} (h : r a b) : IsChain r {a, b} :=
  (isChain_singleton _ _).insert fun _ hb _ => Or.inl <| (eq_of_mem_singleton hb).symm.recOn ‹_›

theorem IsMaxChain.image {r : α → α → Prop} {s : β → β → Prop} (f : r ≃r s) {c : Set α}
    (hc : IsMaxChain r c) : IsMaxChain s (f '' c) where
  left := hc.isChain.image _ _ _ fun _ _ => by exact f.map_rel_iff.2
  right t ht hf :=
    (f.toEquiv.eq_preimage_iff_image_eq _ _).1
      (by
        rw [preimage_equiv_eq_image_symm]
        exact
          hc.2 (ht.image _ _ _ fun _ _ => by exact f.symm.map_rel_iff.2)
            ((f.toEquiv.subset_symm_image _ _).2 hf))

namespace Flag

section LE

variable [LE α] {s t : Flag α} {a : α}

/-- Reinterpret a maximal chain as a flag. -/
def ofIsMaxChain (c : Set α) (hc : IsMaxChain (· ≤ ·) c) : Flag α := ⟨c, hc.isChain, hc.2⟩

@[simp, norm_cast]
theorem coe_ofIsMaxChain (c : Set α) (hc) : ofIsMaxChain c hc = c := rfl

end LE

section Preorder

variable [Preorder α] [Preorder β] {s : Flag α} {a b : α}

theorem mem_iff_forall_le_or_ge : a ∈ s ↔ ∀ ⦃b⦄, b ∈ s → a ≤ b ∨ b ≤ a :=
  ⟨fun ha b => s.le_or_le ha, fun hb =>
    of_not_not fun ha =>
      Set.ne_insert_of_not_mem _ ‹_› <|
        s.maxChain.2 (s.chain_le.insert fun c hc _ => hb hc) <| Set.subset_insert _ _⟩

/-- Flags are preserved under order isomorphisms. -/
def map (e : α ≃o β) : Flag α ≃ Flag β
    where
  toFun s := ofIsMaxChain _ (s.maxChain.image e)
  invFun s := ofIsMaxChain _ (s.maxChain.image e.symm)
  left_inv s := ext <| e.symm_image_image s
  right_inv s := ext <| e.image_symm_image s

@[simp, norm_cast]
theorem coe_map (e : α ≃o β) (s : Flag α) : ↑(map e s) = e '' s :=
  rfl

@[simp]
theorem symm_map (e : α ≃o β) : (map e).symm = map e.symm :=
  rfl

end Preorder

end Flag
