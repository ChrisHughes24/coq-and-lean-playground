import category_theory.adjunction

namespace category_theory

variables {C D : Type*} [category C] [category D]

structure unit_desc (F : C ⥤ D) :=
( obj : D → C )
( unit : Π (X : D), X ⟶ F.obj (obj X) )
( desc : Π {X Y}, (X ⟶ F.obj Y) → (obj X ⟶ Y))
( unit_comp_desc : Π {X Y} (f : X ⟶ F.obj Y), unit X ≫ F.map (desc f) = f )
( desc_unit : Π {X Y} (f : obj X ⟶ Y), desc (unit X ≫ F.map f) = f )

variables {F : C ⥤ D} (ud : unit_desc F)

private lemma unit_desc_ext
  {X : D} {Y : C} {f g : ud.obj X ⟶ Y}
  (H : ud.unit X ≫ F.map f = ud.unit X ≫ F.map g) : f = g :=
by rw [← ud.desc_unit f, H, ud.desc_unit]

def unit_desc.to_functor : D ⥤ C :=
{ obj := ud.obj,
  map := λ X Y f, ud.desc (f ≫ ud.unit Y),
  map_id' := λ X, by rw [category.id_comp, ← category.comp_id (ud.unit X), ← F.map_id,
      ud.desc_unit],
  map_comp' := λ X Y Z f g, unit_desc_ext ud $
    by rw [F.map_comp, ud.unit_comp_desc, ← category.assoc, ud.unit_comp_desc,
      category.assoc, category.assoc, ud.unit_comp_desc] }

def unit_desc.adjunction :
  ud.to_functor ⊣ F :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, ud.unit X ≫ F.map f,
    inv_fun := λ f, ud.desc f,
    left_inv := λ f, ud.desc_unit f,
    right_inv := λ f, ud.unit_comp_desc f },
  hom_equiv_naturality_left_symm' :=
    begin
      intros X' X Y f g,
      dsimp [unit_desc.to_functor],
      apply unit_desc_ext ud,
      rw [ud.unit_comp_desc, F.map_comp, ← category.assoc,
        ud.unit_comp_desc, category.assoc, ud.unit_comp_desc],
    end,
  hom_equiv_naturality_right' :=
    begin
      intros X Y Y' f g,
      dsimp [unit_desc.to_functor],
      rw [F.map_comp, category.assoc]
    end }

structure counit_lift (F : C ⥤ D) :=
( obj : D → C )
( counit : Π (X : D), F.obj (obj X) ⟶ X )
( lift : Π {X Y}, (F.obj X ⟶ Y) → (X ⟶ obj Y))
( lift_comp_counit : Π {X Y} (f : F.obj X ⟶ Y), F.map (lift f) ≫ counit Y = f )
( lift_counit : Π {X Y} (f : X ⟶ obj Y), lift (F.map f ≫ counit Y) = f )

variable (cl : counit_lift F)

private lemma counit_lift_ext
  {X : C} {Y : D} {f g : X ⟶ cl.obj Y}
  (H : F.map f ≫ cl.counit Y = F.map g ≫ cl.counit Y) : f = g :=
by rw [← cl.lift_counit f, H, cl.lift_counit]

def counit_lift.to_functor : D ⥤ C :=
{ obj := cl.obj,
  map := λ X Y f, cl.lift (cl.counit X ≫ f),
  map_id' := λ X, by rw [category.comp_id, ← category.id_comp (cl.counit X), ← F.map_id,
      cl.lift_counit],
  map_comp' := λ X Y Z f g, counit_lift_ext cl $
    by rw [F.map_comp, cl.lift_comp_counit, category.assoc, cl.lift_comp_counit,
      ← category.assoc, ← category.assoc, cl.lift_comp_counit] }

def counit_lift.adjunction :
  F ⊣ cl.to_functor :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, cl.lift f,
    inv_fun := λ f, F.map f ≫ cl.counit Y,
    left_inv := λ f, cl.lift_comp_counit f,
    right_inv := λ f, cl.lift_counit f },
  hom_equiv_naturality_left_symm' :=
    begin
      intros X Y Y' f g,
      dsimp [counit_lift.to_functor],
      rw [F.map_comp, category.assoc]
    end,
  hom_equiv_naturality_right' :=
    begin
      intros X' X Y f g,
      dsimp [counit_lift.to_functor],
      apply counit_lift_ext cl,
      rw [cl.lift_comp_counit, F.map_comp, category.assoc,
        cl.lift_comp_counit, ← category.assoc, cl.lift_comp_counit],
    end }

end category_theory