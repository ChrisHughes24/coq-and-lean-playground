import category_theory.adjunction

open category_theory

variables {C D E : Type} [category.{0} C] [category.{0} D] [category.{0} E]

section unit_extend

structure unit_extend (F : C ⥤ D) :=
( obj : D → C )
( unit : Π (X : D), X ⟶ F.obj (obj X) )
( extend : Π {X Y}, (X ⟶ F.obj Y) → (obj X ⟶ Y))
( unit_comp_extend : Π {X Y} (f : X ⟶ F.obj Y), unit X ≫ F.map (extend f) = f )
( extend_unit : Π {X Y} (f : obj X ⟶ Y), extend (unit X ≫ F.map f) = f )

structure counit_restrict (F : C ⥤ D) :=
( obj : D → C )
( counit : Π (X : D), F.obj (obj X) ⟶ X )
( restrict : Π {X Y}, (F.obj X ⟶ Y) → (X ⟶ obj Y))
( restrict_comp_counit : Π {X Y} (f : F.obj X ⟶ Y), F.map (restrict f) ≫ counit Y = f )
( restrict_counit : Π {X Y} (f : X ⟶ obj Y), restrict (F.map f ≫ counit Y) = f )

variables {F : C ⥤ D} (ue : unit_extend F) (cr : counit_restrict F)

private lemma unit_extend_ext
  {X : D} {Y : C} {f g : ue.obj X ⟶ Y}
  (H : ue.unit X ≫ F.map f = ue.unit X ≫ F.map g) : f = g :=
by rw [← ue.extend_unit f, H, ue.extend_unit]

private lemma counit_restrict_ext
  {X : C} {Y : D} {f g : X ⟶ cr.obj Y}
  (H : F.map f ≫ cr.counit Y = F.map g ≫ cr.counit Y) : f = g :=
by rw [← cr.restrict_counit f, H, cr.restrict_counit]

def left_adjoint_of_unit_extend : D ⥤ C :=
{ obj := ue.obj,
  map := λ X Y f, ue.extend (f ≫ ue.unit Y),
  map_id' := λ X, by rw [category.id_comp, ← category.comp_id (ue.unit X), ← F.map_id,
      ue.extend_unit],
  map_comp' := λ X Y Z f g, unit_extend_ext ue $
    by rw [F.map_comp, ue.unit_comp_extend, ← category.assoc, ue.unit_comp_extend,
      category.assoc, category.assoc, ue.unit_comp_extend] }

def right_adjoint_of_counit_restrict : D ⥤ C :=
{ obj := cr.obj,
  map := λ X Y f, cr.restrict (cr.counit X ≫ f),
  map_id' := λ X, by rw [category.comp_id, ← category.id_comp (cr.counit X), ← F.map_id,
      cr.restrict_counit],
  map_comp' := λ X Y Z f g, counit_restrict_ext cr $
    by rw [F.map_comp, cr.restrict_comp_counit, category.assoc, cr.restrict_comp_counit,
      ← category.assoc, ← category.assoc, cr.restrict_comp_counit] }

def adjunction_of_unit_extend :
  left_adjoint_of_unit_extend ue ⊣ F :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, ue.unit X ≫ F.map f,
    inv_fun := λ f, ue.extend f,
    left_inv := λ f, ue.extend_unit f,
    right_inv := λ f, ue.unit_comp_extend f },
  hom_equiv_naturality_left_symm' :=
    begin
      intros X' X Y f g,
      dsimp [left_adjoint_of_unit_extend],
      apply unit_extend_ext ue,
      rw [ue.unit_comp_extend, F.map_comp, ← category.assoc,
        ue.unit_comp_extend, category.assoc, ue.unit_comp_extend],
    end,
  hom_equiv_naturality_right' :=
    begin
      intros X Y Y' f g,
      dsimp [left_adjoint_of_unit_extend],
      rw [F.map_comp, category.assoc]
    end }

def adjunction_of_counit_restrict :
  F ⊣ right_adjoint_of_counit_restrict cr :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, cr.restrict f,
    inv_fun := λ f, F.map f ≫ cr.counit Y,
    left_inv := λ f, cr.restrict_comp_counit f,
    right_inv := λ f, cr.restrict_counit f },
  hom_equiv_naturality_left_symm' :=
    begin
      intros X Y Y' f g,
      dsimp [right_adjoint_of_counit_restrict],
      rw [F.map_comp, category.assoc]
    end,
  hom_equiv_naturality_right' :=
    begin
      intros X' X Y f g,
      dsimp [right_adjoint_of_counit_restrict],
      apply counit_restrict_ext cr,
      rw [cr.restrict_comp_counit, F.map_comp, category.assoc,
        cr.restrict_comp_counit, ← category.assoc, cr.restrict_comp_counit],
    end }

end unit_extend

section rewrite_rules

variables (F : C ⥤ D) (RF : counit_restrict F) (G : D ⥤ E) (RG : counit_restrict G)

-- restrict_counit

lemma restrict_counit' {X : D} :
  RF.restrict (RF.counit X) = 𝟙 (RF.obj X) :=
by rw [← category.id_comp (RF.counit X), ← F.map_id, RF.restrict_counit]

lemma comp_restrict {X Y : C} {Z : D} (f : X ⟶ Y) (g : F.obj Y ⟶ Z) :
  f ≫ RF.restrict g = RF.restrict (F.map f ≫ g) :=
((adjunction_of_counit_restrict RF).hom_equiv_naturality_left f g).symm

-- lemma restrict_counit' {X : E} :
--   RG.restrict (G.map (RF.counit (RG.obj X)) ≫ RG.counit X) = RF.counit (RG.obj X) :=
-- begin
--   rw [RG.restrict_counit]

-- end


end rewrite_rules
