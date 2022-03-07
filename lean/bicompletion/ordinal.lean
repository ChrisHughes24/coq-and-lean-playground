import data.setoid.basic

universes u

inductive acc2 {α : Type u} (r : α → α → Prop) : α → Type u
| intro (x : α) (h : ∀ y, r y x → acc2 y) : acc2 x

structure ordinal : Type (u + 1) :=
( to_type : Type u )
( r : to_type → to_type → Prop )
( wf : ∀ x : to_type, acc2 r x )
( trans : transitive r )
( total : ∀ x y, r x y ∨ r y x ∨ x = y )
#print acc2.rec_on

namespace ordinal

instance : has_coe_to_sort ordinal.{u} (Type u) :=
{ coe := ordinal.to_type }

instance {α : ordinal.{u}} : linear_order α :=
{ le := λ x y, α.r x y ∨ x = y,
  le_refl := λ _, or.inr rfl,
  le_trans := λ a b c h₁ h₂, 
    h₁.elim 
      (λ h₁, h₂.elim (λ h₂, or.inl (α.trans h₁ h₂)) 
        (λ h₂, h₂ ▸ or.inl h₁)) 
      (λ h₁, h₁.symm ▸ h₂),
  le_antisymm := sorry,
  le_total := sorry,
  decidable_le := sorry }




end ordinal

example (A : Type u) (f : A → ordinal.{u}) : ordinal.{u} :=
{ to_type := quotient (setoid.ker f),
  r := _ }