import category_theory.limits.preserves.basic

open category_theory category_theory.limits

variables (𝓒 : Type) [category.{0} 𝓒]

@[protect_proj] structure thing' : Type 1 :=
(𝓓 : Type)
[𝓓_cat : category.{0} 𝓓]
(of_cat : 𝓒 ⥤ 𝓓)
(full : full of_cat)
(faithful : faithful of_cat)
(rel : 𝓓 → 𝓓 → Prop)
(well_founded_rel : well_founded rel)
-- (comp_rel : ∀ {X Y Z A B : 𝓓} (i : A ⟶ B) (f : X ⟶ Y) (g : Y ⟶ Z),
--   rel ⟨X, Y, f⟩ ⟨A, B, i⟩ → rel ⟨Y, Z, g⟩ ⟨A, B, i⟩ → 
--   rel ⟨X, Z, f ≫ g⟩ ⟨A, B, i⟩)

attribute [instance] thing'.𝓓_cat

variable {𝓒}

-- def smaller {𝕂 : thing' 𝓒} {X Y : 𝕂.𝓓} (f : X ⟶ Y) : Type :=
-- { A : 𝕂.𝓓 // 𝕂.rel ⟨A, A, 𝟙 A⟩ ⟨X, Y, f⟩ }

def smaller {𝕂 : thing' 𝓒} (X : 𝕂.𝓓) : Type :=
{ A : 𝕂.𝓓 // 𝕂.rel A X }

-- instance (𝕂 : thing' 𝓒) {X Y : 𝕂.𝓓} (f : X ⟶ Y) : 
--   category_struct (smaller f) :=
-- { hom := λ A B, { g : A.1 ⟶ B.1 // 𝕂.rel ⟨A.1, B.1, g⟩ ⟨X, Y, f⟩ },
--   id := λ A, ⟨𝟙 A.1, A.2⟩,
--   comp := λ A B C i j, ⟨i.1 ≫ j.1, 𝕂.comp_rel _ _ j.1 i.2 j.2⟩ }

variables {𝕂 : thing' 𝓒}

instance (𝕂 : thing' 𝓒) (X : 𝕂.𝓓) : category_struct (smaller X) :=
{ hom := λ A B, A.1 ⟶ B.1,
  id := λ A, 𝟙 A.1,
  comp := λ A B C i j, i ≫ j }

instance (𝕂 : thing' 𝓒) (X : 𝕂.𝓓) : category (smaller X) := 
{ id_comp' := λ X Y f, @category.id_comp 𝕂.𝓓 _ _ _ f,
  comp_id' := λ X Y f, @category.comp_id 𝕂.𝓓 _ _ _ f,
  assoc' := λ W X Y Z f g h, @category.assoc 𝕂.𝓓 _ _ _ _ _ f g h }

def of_smaller {𝕂 : thing' 𝓒} (X : 𝕂.𝓓) : 

