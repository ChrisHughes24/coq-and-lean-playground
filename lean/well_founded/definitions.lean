import category_theory.limits.preserves.basic
import category_theory.full_subcategory

open category_theory

variables {𝓒 𝓓 : Type} [category.{0} 𝓒] [category.{0} 𝓓] (F : 𝓒 ⥤ 𝓓)

def hom_union (𝓒 : Type) [category.{0} 𝓒] : Type :=
Σ (X Y : 𝓒), (X ⟶ Y)

def of_hom {X Y : 𝓒} (f : X ⟶ Y) : hom_union 𝓒 :=
⟨X, Y, f⟩

variable (𝓓)

class well_founded_extension' [preorder (hom_union 𝓓)] : Type :=
( wf : well_founded ((<) : hom_union 𝓓 → hom_union 𝓓 → Prop) )
( is_presheaf : hom_union 𝓓 → bool )
( comp_lt : ∀ {X Y Z A B : 𝓓} (f : X ⟶ Y) (g : Y ⟶ Z) (i : A ⟶ B),
    of_hom f < of_hom i →
    of_hom g < of_hom i →
    of_hom (f ≫ g) < of_hom i )
( comp_le : ∀ {X Y Z A B : 𝓓} (f : X ⟶ Y) (g : Y ⟶ Z) (i : A ⟶ B),
    of_hom f ≤ of_hom i →
    of_hom g ≤ of_hom i →
    of_hom (f ≫ g) ≤ of_hom i )
( id_left_lt : ∀ {X Y A B : 𝓓} (f : X ⟶ Y) (i : A ⟶ B),
    of_hom f < of_hom i → 
    of_hom (𝟙 X) < of_hom i )
( id_right_lt : ∀ {X Y A B : 𝓓} (f : X ⟶ Y) (i : A ⟶ B),
    of_hom f < of_hom i → 
    of_hom (𝟙 Y) < of_hom i )
( id_left_le : ∀ {X Y A B : 𝓓} (f : X ⟶ Y) (i : A ⟶ B),
    of_hom f ≤ of_hom i → 
    of_hom (𝟙 X) ≤ of_hom i )
( id_right_le : ∀ {X Y A B : 𝓓} (f : X ⟶ Y) (i : A ⟶ B),
    of_hom f ≤ of_hom i → 
    of_hom (𝟙 Y) ≤ of_hom i )

variables {𝓓} [preorder (hom_union 𝓓)]

def lt_cat [well_founded_extension' 𝓓] {A B : 𝓓} (f : A ⟶ B) : Type :=
{ X : 𝓓 // (of_hom (𝟙 X)) < (of_hom f) }

instance [well_founded_extension' 𝓓] {A B : 𝓓} (f : A ⟶ B) : 
  category_struct (lt_cat f) :=
{ hom := λ X Y, { g : X.1 ⟶ Y.1 // of_hom g < of_hom f },
  id := λ X, ⟨𝟙 X.1, X.2⟩,
  comp := λ X Y Z f g, ⟨f.1 ≫ g.1, well_founded_extension'.comp_lt _ _ _ f.2 g.2⟩ }

instance [well_founded_extension' 𝓓] {A B : 𝓓} (f : A ⟶ B) : 
  category (lt_cat f) := 
{ id_comp' := λ X Y f, subtype.eq (category.id_comp f.1),
  comp_id' := λ X Y f, subtype.eq (category.comp_id f.1),
  assoc' := λ W Y X Z f g h, subtype.eq (category.assoc f.1 g.1 h.1) }

def of_lt_cat [well_founded_extension' 𝓓] {A B : 𝓓} (f : A ⟶ B) : 
  lt_cat f ⥤ 𝓓 :=
{ obj := subtype.val,
  map := λ _ _, subtype.val,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

def le_cat [well_founded_extension' 𝓓] {A B : 𝓓} (f : A ⟶ B) : Type :=
{ X : 𝓓 // (of_hom (𝟙 X)) ≤ (of_hom f) }

instance [well_founded_extension' 𝓓] {A B : 𝓓} (f : A ⟶ B) : 
  category_struct (le_cat f) :=
{ hom := λ X Y, { g : X.1 ⟶ Y.1 // of_hom g ≤ of_hom f },
  id := λ X, ⟨𝟙 X.1, X.2⟩,
  comp := λ X Y Z f g, ⟨f.1 ≫ g.1, well_founded_extension'.comp_le _ _ _ f.2 g.2⟩ }

instance [well_founded_extension' 𝓓] {A B : 𝓓} (f : A ⟶ B) : category (le_cat f) := 
{ id_comp' := λ X Y f, subtype.eq (category.id_comp f.1),
  comp_id' := λ X Y f, subtype.eq (category.comp_id f.1),
  assoc' := λ W Y X Z f g h, subtype.eq (category.assoc f.1 g.1 h.1) }

def of_le_cat [well_founded_extension' 𝓓] {A B : 𝓓} (f : A ⟶ B) : 
  le_cat f ⥤ 𝓓 :=
{ obj := subtype.val,
  map := λ _ _, subtype.val,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ _ _, rfl }

open well_founded_extension'

class well_founded_extension (F : 𝓒 ⥤ 𝓓) extends well_founded_extension' 𝓓 :=
( presheaf : Π {A B : 𝓓} (f : A ⟶ B) (X Y : le_cat f) (g : X ⟶ Y), 
      )

-- structure well_founded_extension : Type :=
-- ( rel : 𝓓 → 𝓓 → Prop )
-- ( wf : well_founded rel )
-- ( is_presheaf : 𝓓 → bool )
-- ( rel_hom : Π {X Y : 𝓓}, (X ⟶ Y) → 𝓓 )
-- ( rel_hom_id : ∀ (X : 𝓓), rel_hom (𝟙 X) = X )
-- ( rel_hom_comp : ∀ {X Y Z A : 𝓓} (f : X ⟶ Y) (g : Y ⟶ Z),
--     rel (rel_hom f) A → rel (rel_hom g) A → rel (rel_hom (f ≫ g)) A )
-- ( to_presheaf : ∀ (A X Y : 𝓓) (hXA : rel X A) (hYA : rel Y A)
--      (f : X ⟶ Y), 
--      )


