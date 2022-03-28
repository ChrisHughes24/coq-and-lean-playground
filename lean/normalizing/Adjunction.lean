import tactic

@[derive decidable_eq] def free_cat : Type := ℕ 

namespace free_cat

@[derive decidable_eq] inductive hom : free_cat → free_cat → Type
| id : Π (A : free_cat), hom A A
| cons : Π {A B C : free_cat}, ℕ → hom B C → hom A C

def comp : Π {A B C : free_cat} (f : hom A B) (g : hom B C), hom A C
| _ _ _ (hom.id _) g := g
| _ _ _ (hom.cons n f) g := hom.cons n (comp f g)

@[simp] lemma id_comp {A B : free_cat} (f : hom A B) : comp (hom.id A) f = f := rfl

@[simp] lemma comp_id {A B : free_cat} (f : hom A B) : comp f (hom.id B) = f :=
by { induction f; simp [*, comp] }

lemma comp_assoc {A B C D : free_cat} (f : hom A B) (g : hom B C) (h : hom C D) :
  comp f (comp g h) = comp (comp f g) h :=
by induction f; simp [comp, *]

end free_cat
