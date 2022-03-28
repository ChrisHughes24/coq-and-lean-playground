import category_theory.limits.preserves.basic

open category_theory category_theory.limits

constant bicompletion (𝓒 : Type) [category.{0} 𝓒] : Type 1

namespace bicompletion

variables (𝓒 : Type) [category.{0} 𝓒]

@[instance] protected constant category : category.{0} (bicompletion 𝓒)

constant of_cat : 𝓒 ⥤ bicompletion 𝓒

@[instance] protected constant full : full (of_cat 𝓒)

@[instance] protected constant has_limits : has_limits_of_size.{0 0} (bicompletion 𝓒)

@[instance] protected constant has_colimits : has_colimits_of_size.{0 0} (bicompletion 𝓒)

variables {𝓒} {𝓓 : Type 1} [category.{0} 𝓓] [has_limits_of_size.{0 0} 𝓓]
  [has_colimits_of_size.{0 0} 𝓓] (F : 𝓒 ⥤ 𝓓)

constant extend (F : 𝓒 ⥤ 𝓓) : bicompletion 𝓒 ⥤ 𝓓

namespace extend

@[instance] protected constant preserves_limits : 
  preserves_limits_of_size.{0 0} (extend F) 

@[instance] protected constant preserves_colimits : 
  preserves_colimits_of_size.{0 0} (extend F) 

constant commutes : of_cat 𝓒 ⋙ extend F ≅ F

end extend

end bicompletion

@[derive decidable_eq] def free_cat : Type := ℕ 

namespace free_cat

def of_nat_obj : ℕ → free_cat := id

@[derive decidable_eq] inductive hom : free_cat → free_cat → Type
| id : Π (A : free_cat), hom A A
| cons : Π (A : free_cat) {B C : free_cat}, ℕ → hom B C → hom A C

def of_nat_hom (A B : ℕ) (f : ℕ) : hom (of_nat_obj A) (of_nat_obj B) :=
hom.cons A f (hom.id B)

def comp : Π {A B C : free_cat} (f : hom A B) (g : hom B C), hom A C
| _ _ _ (hom.id _) g := g
| _ _ _ (hom.cons _ n f) g := hom.cons _ n (comp f g)

@[simp] protected lemma id_comp {A B : free_cat} (f : hom A B) : comp (hom.id A) f = f := rfl

@[simp] protected lemma comp_id {A B : free_cat} (f : hom A B) : comp f (hom.id B) = f :=
by { induction f; simp [*, comp] }

protected lemma comp_assoc {A B C D : free_cat} (f : hom A B) (g : hom B C) (h : hom C D) :
  comp (comp f g) h = comp f (comp g h) :=
by induction f; simp [comp, *]

instance : category_struct free_cat := 
{ hom := hom,
  id := hom.id,
  comp := λ _ _ _, comp }

instance : category free_cat := 
{ id_comp' := by intros; apply free_cat.id_comp,
  comp_id' := by intros; apply free_cat.comp_id,
  assoc' := by intros; apply free_cat.comp_assoc }

def extend (𝓒 : Type*) [category 𝓒] (obj : ℕ → 𝓒) (hom : Π (A B : ℕ) (f : ℕ), (obj A) ⟶ obj B) :
  free_cat ⥤ 𝓒 :=
{ obj := obj,
  map := λ A B f, @free_cat.hom.rec_on 
    (λ (A B : ℕ) (f : free_cat.hom A B), obj A ⟶ obj B) A B f 
    (λ A, 𝟙 (obj A)) (λ A B C f g ih, hom A B f ≫ ih),
  map_comp' := begin
    intros X Y Z f g,
    dsimp,
    induction f,
    { dsimp,
      rw [category.id_comp],
      refl },
    { dsimp,
      rw [category.assoc],
      rw [← f_ih],
      refl }
  end, }

variables (𝓒 : Type*) [category 𝓒] (obj : ℕ → 𝓒) (hom : Π (A B : ℕ) (f : ℕ), (obj A) ⟶ obj B)

lemma extend_obj (A : ℕ) : (extend 𝓒 obj hom).obj (of_nat_obj A) = obj A := rfl

lemma extend_hom (A B : ℕ) (f : ℕ) : (extend 𝓒 obj hom).map (of_nat_hom A B f) = hom A B f := 
category.comp_id _

-- lemma extend_unique (F : free_cat ⥤ 𝓒) (hobj : ∀ X, F.obj (of_nat_obj X) = obj X)
--   (hhom : ∀ (A B : ℕ) (f : ℕ), F.map (of_nat_hom A B f) = hom A B f) : 

end free_cat

inductive pc 
