import category_theory.adjunction
import category_theory.comma
import category_theory.punit
import category_theory.limits.types

open category_theory opposite

variables (C : Type) [category.{0} C] (F : C ⥤ Type) (G : Cᵒᵖ ⥤ Type)

def presheaf_to_copresheaf : (Cᵒᵖ ⥤ Type) ⥤ (C ⥤ Type)ᵒᵖ :=
functor.right_op (coyoneda ⋙ (whiskering_left C (Cᵒᵖ ⥤ Type) Type).obj yoneda)

def copresheaf_to_presheaf : (C ⥤ Type)ᵒᵖ ⥤ (Cᵒᵖ ⥤ Type) :=
coyoneda ⋙ (whiskering_left Cᵒᵖ (C ⥤ Type) Type).obj coyoneda

local attribute [simp] copresheaf_to_presheaf presheaf_to_copresheaf

example : presheaf_to_copresheaf C ⊣ copresheaf_to_presheaf C :=
adjunction.mk_of_unit_counit
  { unit :=
    { app := λ F,
      { app := λ X FX,
        { app := λ Y f, f.app X FX },
          naturality' := begin
            intros X Y f,
            ext FX Z g,
            dsimp at *,
            exact function.funext_iff.1 (g.naturality f) FX
          end } },
    counit :=
    { app := λ F, show op (unop ((presheaf_to_copresheaf C).obj
          ((copresheaf_to_presheaf C).obj F))) ⟶ op (unop F),
        from quiver.hom.op
      { app := λ X FX,
        { app := λ Y f, f.app X FX },
          naturality' := begin
            intros X Y f,
            ext FX Z g,
            dsimp at *,
            exact function.funext_iff.1 (g.naturality f) FX
          end } },
    left_triangle' := begin
      ext F,
      dsimp [presheaf_to_copresheaf, copresheaf_to_presheaf],
      refine quiver.hom.unop_inj _,
      ext, refl
    end,
    right_triangle' := by { ext, refl } }

def as_cone (X : C) : limits.cone (comma.snd ((category_theory.functor.const (discrete unit)).obj X) (𝟭 C)) :=
{ X := X,
  π :=
  { app := λ Y, Y.hom,
    naturality' := λ Y Z f, f.3 } }

def is_limit_as_cone (X : C) : limits.is_limit (as_cone C X) :=
{ lift := λ s, s.2.app ⟨(), X, 𝟙 X⟩,
  fac' := λ s j, begin
      dsimp [as_cone],
      let f : (⟨(), X, 𝟙 X⟩ : comma ((category_theory.functor.const (discrete unit)).obj X) (𝟭 C)) ⟶ j :=
        ⟨⟨⟨subsingleton.elim _ _⟩⟩, j.hom, by tidy⟩,
      have := (@s.2.naturality f).symm,
      dsimp at *,
      simp [this]
    end,
  uniq' := λ s m h, begin
    dsimp [as_cone] at *,
    rw ← h,
    simp,
  end }

def iso_of_preserves_limits (F : Cᵒᵖ ⥤ Type) [limits.preserves_limits F] :
  F ≅ (copresheaf_to_presheaf C).obj ((presheaf_to_copresheaf C).obj F) :=
nat_iso.of_components
  (λ X,
    { hom := λ FX, { app := λ Y f, f.app X FX },
      inv := λ f,
      --  let s : limits.cone (comma.snd ((category_theory.functor.const (discrete unit)).obj X) (𝟭 Cᵒᵖ) ⋙ F) :=
      --   { X := unit,
      --     π :=
      --     { app := λ Y g, begin
      --         dsimp at *,
      --         have := g.app,
      --         dsimp at *,

      --     end } },

      begin
        dsimp at *,
        have := f.app,
        dsimp at this,
        apply (limits.is_limit_of_preserves F (is_limit_as_cone Cᵒᵖ X)).lift
          (limits.limit.cone _),
        dsimp [as_cone] at *,
        tidy,
        have := f.app (unop j.right),
        rcases j with ⟨⟨⟩, j, g⟩,
        dsimp at *,
        dsimp at this,
        have := this _,


      end }  )
  _

variable {C}

structure corepresentation :=
( corepr : C )
( unit : F.obj corepr )
( extend : Π {X : C}, F.obj X → (corepr ⟶ X) )
( map_extend_unit {X : C} (f : F.obj X) : F.map (extend f) unit = f )
( unit_map_extend {X : C} (f : corepr ⟶ X) : extend (F.map f unit) = f )

def hom_ext {R : corepresentation F} {X : C} {f g : R.corepr ⟶ X}
  (h : F.map f R.unit = F.map g R.unit) : f = g :=
by rw [← R.unit_map_extend f, h, R.unit_map_extend]

example (R : corepresentation F) {X Y : C} (f : F.obj X) (g : X ⟶ Y) :
  R.extend f ≫ g = R.extend (F.map g f) :=
hom_ext _ $ by simp [R.map_extend_unit]

def is_repr (R : corepresentation F) : (coyoneda.obj (op R.corepr)) ≅ F :=
nat_iso.of_components
  (λ X, { hom := λ f, F.map f R.unit,
          inv := λ f, R.extend f,
          hom_inv_id' := by funext x; simp [R.unit_map_extend],
          inv_hom_id' := by funext x; simp [R.map_extend_unit] })
  begin
    intros X Y f,
    funext x,
    simp
  end

structure corepresentation2 :=
( corepr : C )
( unit : F.obj corepr )
( extend : Π {X : C}, F.obj X → (corepr ⟶ X) )
( map_extend_unit {X : C} (f : F.obj X) : F.map (extend f) unit = f )
( extend_unit : extend unit = 𝟙 corepr )
( extend_comp {X Y : C} (f : F.obj X) (g : X ⟶ Y) : extend f ≫ g = extend (F.map g f) )

example (R : corepresentation2 F) : corepresentation F :=
{ unit_map_extend := begin
    intros X f,
    rw [← R.extend_comp, R.extend_unit, category.id_comp],
  end
  ..R }

structure representation2 :=
( repr : C )
( counit : G.obj (op repr) )
( restrict : Π {X : C}, G.obj (op X) → (X ⟶ repr ) )
( map_restrict_counit {X : C} (f : G.obj (op X)) : G.map ((restrict f).op) counit = f )
( restrict_counit : restrict counit = 𝟙 repr )
( comp_restrict {X Y : C} (f : G.obj (op X)) (g : Y ⟶ X) : g ≫ restrict f = restrict (G.map g.op f) )

example (R : representation2 G) : corepresentation2 (presheaf_to_copresheaf G) :=
{ corepr := R.repr,
  unit := begin
    dsimp [presheaf_to_copresheaf],
    have := R.counit,

  end, }