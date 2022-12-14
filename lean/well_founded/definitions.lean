import category_theory.limits.preserves.basic
import category_theory.full_subcategory
import category_theory.yoneda

open category_theory

variables {đ đ : Type} [category.{0} đ] [category.{0} đ] (F : đ âĽ¤ đ)

def hom_union (đ : Type) [category.{0} đ] : Type :=
ÎŁ (X Y : đ), (X âś Y)

def of_hom {X Y : đ} (f : X âś Y) : hom_union đ :=
â¨X, Y, fâŠ

variable (đ)

class well_founded_extension' [preorder (hom_union đ)] : Type :=
( wf : well_founded ((<) : hom_union đ â hom_union đ â Prop) )
( is_presheaf : hom_union đ â bool )
( comp_lt : â {X Y Z A B : đ} (f : X âś Y) (g : Y âś Z) (i : A âś B),
    of_hom f < of_hom i â
    of_hom g < of_hom i â
    of_hom (f âŤ g) < of_hom i )
( comp_le : â {X Y Z A B : đ} (f : X âś Y) (g : Y âś Z) (i : A âś B),
    of_hom f â¤ of_hom i â
    of_hom g â¤ of_hom i â
    of_hom (f âŤ g) â¤ of_hom i )
( id_left_lt : â {X Y A B : đ} (f : X âś Y) (i : A âś B),
    of_hom f < of_hom i â 
    of_hom (đ X) < of_hom i )
( id_right_lt : â {X Y A B : đ} (f : X âś Y) (i : A âś B),
    of_hom f < of_hom i â 
    of_hom (đ Y) < of_hom i )
( id_left_le : â {X Y A B : đ} (f : X âś Y) (i : A âś B),
    of_hom f â¤ of_hom i â 
    of_hom (đ X) â¤ of_hom i )
( id_right_le : â {X Y A B : đ} (f : X âś Y) (i : A âś B),
    of_hom f â¤ of_hom i â 
    of_hom (đ Y) â¤ of_hom i )

variables {đ} [preorder (hom_union đ)]

def lt_cat [well_founded_extension' đ] {A B : đ} (f : A âś B) : Type :=
{ X : đ // (of_hom (đ X)) < (of_hom f) }

instance [well_founded_extension' đ] {A B : đ} (f : A âś B) : category_struct (lt_cat f) :=
{ hom := Îť X Y, { g : X.1 âś Y.1 // of_hom g < of_hom f },
  id := Îť X, â¨đ X.1, X.2âŠ,
  comp := Îť X Y Z f g, â¨f.1 âŤ g.1, well_founded_extension'.comp_lt _ _ _ f.2 g.2âŠ }

instance [well_founded_extension' đ] {A B : đ} (f : A âś B) : category (lt_cat f) := 
{ id_comp' := Îť X Y f, subtype.eq (category.id_comp f.1),
  comp_id' := Îť X Y f, subtype.eq (category.comp_id f.1),
  assoc' := Îť W Y X Z f g h, subtype.eq (category.assoc f.1 g.1 h.1) }

def of_lt_cat [well_founded_extension' đ] {A B : đ} (f : A âś B) : lt_cat f âĽ¤ đ :=
{ obj := subtype.val,
  map := Îť _ _, subtype.val,
  map_id' := Îť _, rfl,
  map_comp' := Îť _ _ _ _ _, rfl }

def le_cat [well_founded_extension' đ] {A B : đ} (f : A âś B) : Type :=
{ X : đ // (of_hom (đ X)) â¤ (of_hom f) }

instance [well_founded_extension' đ] {A B : đ} (f : A âś B) : category_struct (le_cat f) :=
{ hom := Îť X Y, { g : X.1 âś Y.1 // of_hom g â¤ of_hom f },
  id := Îť X, â¨đ X.1, X.2âŠ,
  comp := Îť X Y Z f g, â¨f.1 âŤ g.1, well_founded_extension'.comp_le _ _ _ f.2 g.2âŠ }

instance [well_founded_extension' đ] {A B : đ} (f : A âś B) : category (le_cat f) := 
{ id_comp' := Îť X Y f, subtype.eq (category.id_comp f.1),
  comp_id' := Îť X Y f, subtype.eq (category.comp_id f.1),
  assoc' := Îť W Y X Z f g h, subtype.eq (category.assoc f.1 g.1 h.1) }

def of_le_cat [well_founded_extension' đ] {A B : đ} (f : A âś B) : le_cat f âĽ¤ đ :=
{ obj := subtype.val,
  map := Îť _ _, subtype.val,
  map_id' := Îť _, rfl,
  map_comp' := Îť _ _ _ _ _, rfl }

open well_founded_extension'

class well_founded_extension (F : đ âĽ¤ đ) extends well_founded_extension' đ :=
( presheaf : Î  {A B : đ} (f : A âś B) (h : is_presheaf (of_hom f) = tt) (X Y : le_cat f),
    (X âś Y) âŞ (((of_lt_cat f).op â (of_le_cat f â yoneda).obj X) âś 
                ((of_lt_cat f).op â (of_le_cat f â yoneda).obj Y)))
( copresheaf : Î  {A B : đ} (f : A âś B) (h : is_presheaf (of_hom f) = ff) (X Y : le_cat f),
    (X âś Y) âŞ (((of_lt_cat f).op â 
      (of_le_cat f â coyoneda.right_op â functor.op_hom đ Type).obj X) âś 
                ((of_lt_cat f).op â 
      (of_le_cat f â coyoneda.right_op â functor.op_hom đ Type).obj Y)))
