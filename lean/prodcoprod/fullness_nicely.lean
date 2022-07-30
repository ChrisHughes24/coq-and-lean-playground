import .presheaves

open category_theory opposite

noncomputable theory

variables (C : Type) [category.{0} C]

inductive prod_coprod : Type
| of_cat' : C → prod_coprod
| prod : prod_coprod → prod_coprod → prod_coprod
| coprod : prod_coprod → prod_coprod → prod_coprod

variable {C}

namespace prod_coprod

inductive hom_syntax : Π (X Y : prod_coprod C), Type
| of_cat {X Y : C} : (X ⟶ Y) → hom_syntax (of_cat' X) (of_cat' Y)
| prod_mk {X Y Z : prod_coprod C} : hom_syntax X Y → hom_syntax X Z → hom_syntax X (Y.prod Z)
| fst {X Y : prod_coprod C} : hom_syntax (X.prod Y) X
| snd {X Y : prod_coprod C} : hom_syntax (X.prod Y) Y
| coprod_mk {X Y Z : prod_coprod C} : hom_syntax X Z → hom_syntax Y Z → hom_syntax (X.coprod Y) Z
| inl {X Y : prod_coprod C} : hom_syntax X (X.coprod Y)
| inr {X Y : prod_coprod C} : hom_syntax Y (X.coprod Y)
| id (X : prod_coprod C) : hom_syntax X X
| comp {X Y Z : prod_coprod C} : hom_syntax X Y → hom_syntax Y Z → hom_syntax X Z

namespace hom_syntax

inductive rel : Π {X Y : prod_coprod C}, hom_syntax X Y → hom_syntax X Y → Prop
| refl {X Y : prod_coprod C} (f : hom_syntax X Y) : rel f f
| symm {X Y : prod_coprod C} {f g : hom_syntax X Y} : rel f g → rel g f
| trans {X Y : prod_coprod C} {f g h : hom_syntax X Y} : rel f g → rel g h → rel f h
| comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : hom_syntax X Y} {g₁ g₂ : hom_syntax Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp g₁) (f₂.comp g₂)
| prod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : hom_syntax X Y} {g₁ g₂ : hom_syntax X Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.prod_mk g₁) (f₂.prod_mk g₂)
| coprod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : hom_syntax X Z} {g₁ g₂ : hom_syntax Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.coprod_mk g₁) (f₂.coprod_mk g₂)
| id_comp {X Y : prod_coprod C} (f : hom_syntax X Y) : rel ((hom_syntax.id X).comp f) f
| comp_id {X Y : prod_coprod C} (f : hom_syntax X Y) : rel (f.comp (hom_syntax.id Y)) f
| assoc {W X Y Z : prod_coprod C} (f : hom_syntax W X) (g : hom_syntax X Y) (h : hom_syntax Y Z) :
  rel ((f.comp g).comp h) (f.comp (g.comp h))
| of_cat_id {X : C} : rel (hom_syntax.of_cat (𝟙 X)) (hom_syntax.id (of_cat' X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  rel (hom_syntax.of_cat (f ≫ g)) (hom_syntax.comp (hom_syntax.of_cat f) (hom_syntax.of_cat g))
| mk_comp_fst {X Y Z : prod_coprod C} (f : hom_syntax X Y) (g : hom_syntax X Z) :
  rel (hom_syntax.comp (hom_syntax.prod_mk f g) hom_syntax.fst) f
| mk_comp_snd {X Y Z : prod_coprod C} (f : hom_syntax X Y) (g : hom_syntax X Z) :
  rel (hom_syntax.comp (hom_syntax.prod_mk f g) hom_syntax.snd) g
| prod_eta {X Y Z : prod_coprod C} (f : hom_syntax X (Y.prod Z)) :
  rel (hom_syntax.prod_mk (f.comp hom_syntax.fst) (f.comp hom_syntax.snd)) f
| inl_comp_mk {X Y Z : prod_coprod C} (f : hom_syntax X Z) (g : hom_syntax Y Z) :
  rel (hom_syntax.comp hom_syntax.inl (hom_syntax.coprod_mk f g)) f
| inr_comp_mk {X Y Z : prod_coprod C} (f : hom_syntax X Z) (g : hom_syntax Y Z) :
  rel (hom_syntax.comp hom_syntax.inr (hom_syntax.coprod_mk f g)) g
| coprod_eta {X Y Z : prod_coprod C} (f : hom_syntax (X.coprod Y) Z) :
  rel (hom_syntax.coprod_mk (hom_syntax.inl.comp f) (hom_syntax.inr.comp f)) f

attribute [refl] rel.refl
attribute [symm] rel.symm
attribute [trans] rel.trans

infixl ` ♥ `: 50 := rel

lemma rel_prod {X Y Z : prod_coprod C} {f g : hom_syntax X (Y.prod Z)}
  (h₁ : rel (f.comp hom_syntax.fst) (g.comp hom_syntax.fst))
  (h₂ : rel (f.comp hom_syntax.snd) (g.comp hom_syntax.snd)) :
  rel f g :=
calc f ♥ hom_syntax.prod_mk (f.comp hom_syntax.fst) (f.comp hom_syntax.snd) : rel.symm (rel.prod_eta f)
   ... ♥ hom_syntax.prod_mk (g.comp hom_syntax.fst) (g.comp hom_syntax.snd) : rel.prod_mk_congr h₁ h₂
   ... ♥ g : rel.prod_eta g

lemma rel_coprod {X Y Z : prod_coprod C} {f g : hom_syntax (X.coprod Y) Z}
  (h₁ : rel (hom_syntax.inl.comp f) (hom_syntax.inl.comp g))
  (h₂ : rel (hom_syntax.inr.comp f) (hom_syntax.inr.comp g)) :
  rel f g :=
calc f ♥ hom_syntax.coprod_mk (hom_syntax.inl.comp f) (hom_syntax.inr.comp f) : rel.symm (rel.coprod_eta f)
   ... ♥ hom_syntax.coprod_mk (hom_syntax.inl.comp g) (hom_syntax.inr.comp g) : rel.coprod_mk_congr h₁ h₂
   ... ♥ g : rel.coprod_eta g

instance rel_setoid (X Y : prod_coprod C) : setoid (hom_syntax X Y) :=
{ r := rel,
  iseqv := ⟨rel.refl, λ _ _, rel.symm, λ _ _ _, rel.trans⟩ }

end hom_syntax

section hom_syntax

open hom_syntax

def hom (X Y : prod_coprod C) : Type := quotient (hom_syntax.rel_setoid X Y)

instance : category_struct (prod_coprod C) :=
{ hom := hom,
  id := λ X, quotient.mk' (hom_syntax.id X),
  comp := λ X Y Z f g, quotient.lift_on₂ f g (λ f g, quotient.mk' (hom_syntax.comp f g))
    (λ f₁ g₁ f₂ g₂ hf hg, quotient.sound (rel.comp_congr hf hg)) }

instance : category (prod_coprod C) :=
{ id_comp' := λ X Y f, quotient.induction_on f (λ f, quotient.sound (rel.id_comp f)),
  comp_id' := λ X Y f, quotient.induction_on f (λ f, quotient.sound (rel.comp_id f)),
  assoc' := λ W X Y Z f g h, quotient.induction_on₃ f g h
    (λ f g h, quotient.sound (rel.assoc f g h)) }

def of_syntax {X Y : prod_coprod C} : hom_syntax X Y → (X ⟶ Y) := quotient.mk

def of_cat : C ⥤ prod_coprod C :=
{ obj := λ X, of_cat' X,
  map := λ X Y f, of_syntax (hom_syntax.of_cat f),
  map_id' := λ X, quotient.sound rel.of_cat_id,
  map_comp' := λ X Y Z f g, quotient.sound (rel.of_cat_comp f g) }

@[simp] lemma of_cat_obj (X : C) : of_cat.obj X = of_cat' X := rfl

def to_presheaf_obj (X : prod_coprod C) : (Cᵒᵖ ⥤ Type) :=
prod_coprod.rec_on X
  yoneda.obj
  (λ X Y ih₁ ih₂, Pprod ih₁ ih₂)
  (λ X Y ih₁ ih₂, Pcoprod ih₁ ih₂)

def prod_mk {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) : X ⟶ (Y.prod Z) :=
quotient.lift_on₂ f g (λ f g, of_syntax (prod_mk f g)) begin
  intros,
  dsimp,
  refine quotient.sound _,
  refine rel.prod_mk_congr _ _; assumption
end

def fst {X Y : prod_coprod C} : (X.prod Y) ⟶ X :=
of_syntax fst

def snd {X Y : prod_coprod C} : (X.prod Y) ⟶ Y :=
of_syntax snd

@[simp] lemma prod_mk_comp_fst {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ fst = f :=
quotient.induction_on₂ f g (λ f g, quotient.sound (hom_syntax.rel.mk_comp_fst _ _))

@[simp] lemma prod_mk_comp_snd {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ snd = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (hom_syntax.rel.mk_comp_snd _ _))

lemma prod_mk_eta {X Y Z : prod_coprod C} (f : X ⟶ Y.prod Z) :
  prod_mk (f ≫ fst) (f ≫ snd) = f :=
quotient.induction_on f (λ f, quotient.sound (hom_syntax.rel.prod_eta _))

@[ext] lemma prod_hom_ext {X Y Z : prod_coprod C} {f g : X ⟶ Y.prod Z}
  (h₁ : f ≫ fst = g ≫ fst) (h₂ : f ≫ snd = g ≫ snd) : f = g :=
begin
  conv_lhs { rw ← prod_mk_eta f },
  rw [h₁, h₂, prod_mk_eta]
end

def coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) : (X.coprod Y) ⟶ Z :=
quotient.lift_on₂ f g (λ f g, of_syntax (coprod_mk f g)) begin
  intros,
  dsimp,
  refine quotient.sound _,
  refine rel.coprod_mk_congr _ _; assumption
end

def inl {X Y : prod_coprod C} : X ⟶ (X.coprod Y) :=
of_syntax inl

def inr {X Y : prod_coprod C} : Y ⟶ (X.coprod Y) :=
of_syntax inr

@[elab_as_eliminator] lemma hom_induction
  {motive : Π (X Y : prod_coprod C), (X ⟶ Y) → Prop}
  {X Y : prod_coprod C} (f : X ⟶ Y)
  (h₁ : Π {X Y : C} (f : X ⟶ Y), motive _ _ (of_cat.map f))
  (h₂ : Π {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z),
     motive X Y f → motive X Z g → motive _ _ (prod_mk f g))
  (h₃ : Π {X Y : prod_coprod C}, motive (X.prod Y) X fst)
  (h₄ : Π {X Y : prod_coprod C}, motive (X.prod Y) Y snd)
  (h₅ : Π {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z),
     motive X Z f → motive Y Z g → motive _ _ (coprod_mk f g))
  (h₆ : Π {X Y : prod_coprod C}, motive X (X.coprod Y) inl)
  (h₇ : Π {X Y : prod_coprod C}, motive Y (X.coprod Y) inr)
  (h₈ : Π (X : prod_coprod C), motive X X (𝟙 X))
  (h₉ : Π {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : Y ⟶ Z),
     motive X Y f → motive Y Z g → motive X Z (f ≫ g)) :
  motive X Y f :=
quotient.induction_on f
  begin
    intro f,
    apply hom_syntax.rec_on f; try { assumption },
    { intros _ _ _ f g,
      exact h₂ (of_syntax f) (of_syntax g) },
    { intros _ _ _ f g,
      exact h₅ (of_syntax f) (of_syntax g) },
    { intros _ _ _ f g,
      exact h₉ (of_syntax f) (of_syntax g) }
  end

@[simp] lemma inl_comp_coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inl ≫ coprod_mk f g = f :=
quotient.induction_on₂ f g (λ f g, quotient.sound (hom_syntax.rel.inl_comp_mk _ _))

@[simp] lemma inr_comp_coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inr ≫ coprod_mk f g = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (hom_syntax.rel.inr_comp_mk _ _))

lemma coprod_mk_eta {X Y Z : prod_coprod C} (f : X.coprod Y ⟶ Z) :
  coprod_mk (inl ≫ f) (inr ≫ f) = f :=
quotient.induction_on f (λ f, quotient.sound (hom_syntax.rel.coprod_eta _))

@[ext] lemma coprod_hom_ext {X Y Z : prod_coprod C} {f g : X.coprod Y ⟶ Z}
  (h₁ : inl ≫ f = inl ≫ g ) (h₂ : inr ≫ f = inr ≫ g) : f = g :=
begin
  conv_lhs { rw ← coprod_mk_eta f },
  rw [h₁, h₂, coprod_mk_eta]
end

@[simp] def to_presheaf_hom_syntax : Π {X Y : prod_coprod C}, hom_syntax X Y →
  ((to_presheaf_obj X) ⟶ (to_presheaf_obj Y))
| _ _ (hom_syntax.of_cat f) := yoneda.map f
| _ _ (hom_syntax.prod_mk f g) := Pprod_lift (to_presheaf_hom_syntax f) (to_presheaf_hom_syntax g)
| _ _ (hom_syntax.fst) := Pprod_fst
| _ _ (hom_syntax.snd) := Pprod_snd
| _ _ (hom_syntax.coprod_mk f g) := Pcoprod_lift (to_presheaf_hom_syntax f) (to_presheaf_hom_syntax g)
| _ _ (hom_syntax.inl) := Pcoprod_inl
| _ _ (hom_syntax.inr) := Pcoprod_inr
| _ _ (hom_syntax.id X) := 𝟙 _
| _ _ (hom_syntax.comp f g) := to_presheaf_hom_syntax f ≫ to_presheaf_hom_syntax g

lemma to_presheaf_hom_syntax_comp {X Y Z : prod_coprod C} (f : hom_syntax X Y) (g : hom_syntax Y Z) :
  to_presheaf_hom_syntax (f.comp g) = to_presheaf_hom_syntax f ≫ to_presheaf_hom_syntax g := rfl

lemma to_presheaf_hom_syntax_rel {X Y : prod_coprod C} (f g : hom_syntax X Y) (h : rel f g) :
  to_presheaf_hom_syntax f = to_presheaf_hom_syntax g :=
begin
  induction h; try { simp * }; try { ext }; try { refl }; tidy,
end

def to_presheaf : prod_coprod C ⥤ (Cᵒᵖ ⥤ Type) :=
{ obj := to_presheaf_obj,
  map := λ X Y f, quotient.lift_on f (to_presheaf_hom_syntax) to_presheaf_hom_syntax_rel,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ f g, quotient.induction_on₂ f g begin intros, simp,
    erw quotient.lift_on_mk,
    simp [to_presheaf_hom_syntax_comp] end }

@[simp] lemma to_presheaf_obj_of_cat (X : C) : to_presheaf.obj (of_cat' X) = yoneda.obj X := rfl

@[simp] lemma to_presheaf_obj_prod (X Y : prod_coprod C) : to_presheaf.obj (prod X Y) =
  Pprod (to_presheaf_obj X) (to_presheaf_obj Y) := rfl

@[simp] lemma to_presheaf_obj_coprod (X Y : prod_coprod C) : to_presheaf.obj (coprod X Y) =
  Pcoprod (to_presheaf_obj X) (to_presheaf_obj Y) := rfl

@[simp] lemma to_presheaf_of_cat {X Y : C} (f : X ⟶ Y) :
  to_presheaf.map (of_cat.map f) = yoneda.map f := rfl

@[simp] lemma to_presheaf_prod_mk {X Y Z : prod_coprod C}
  (f : X ⟶ Y) (g : X ⟶ Z) :
  to_presheaf.map (prod_mk f g) = Pprod_lift (to_presheaf.map f) (to_presheaf.map g) :=
begin
  refine quotient.induction_on₂ f g _,
  intros, refl
end

@[simp] lemma to_presheaf_coprod_mk {X Y Z : prod_coprod C}
  (f : X ⟶ Z) (g : Y ⟶ Z) :
  to_presheaf.map (coprod_mk f g) = Pcoprod_lift (to_presheaf.map f) (to_presheaf.map g) :=
begin
  refine quotient.induction_on₂ f g _,
  intros, refl
end

@[simp] lemma to_presheaf_fst {X Y : prod_coprod C} :
  to_presheaf.map (fst : X.prod Y ⟶ X) = Pprod_fst := rfl

@[simp] lemma to_presheaf_snd {X Y : prod_coprod C} :
  to_presheaf.map (snd : X.prod Y ⟶ Y) = Pprod_snd := rfl

@[simp] lemma to_presheaf_inl {X Y : prod_coprod C} :
  to_presheaf.map (inl : X ⟶ X.coprod Y) = Pcoprod_inl := rfl

@[simp] lemma to_presheaf_inr {X Y : prod_coprod C} :
  to_presheaf.map (inr : Y ⟶ X.coprod Y) = Pcoprod_inr := rfl

end hom_syntax

def transformation_syntax : Π {X : C} {Y : prod_coprod C}, (to_presheaf.obj Y).obj (opposite.op X) →
  hom_syntax (of_cat' X) Y
| X (of_cat' Y) := λ f, hom_syntax.of_cat f
| X (prod Y Z) := λ f, hom_syntax.prod_mk (transformation_syntax f.1) (transformation_syntax f.2)
| X (coprod Y Z) := λ f, f.elim
  (λ f, (transformation_syntax f).comp hom_syntax.inl)
  (λ f, (transformation_syntax f).comp hom_syntax.inr)

@[simp] def transformation : Π {X : C} {Y : prod_coprod C},
  (to_presheaf.obj Y).obj (opposite.op X) →
  ((of_cat' X) ⟶ Y)
| X (of_cat' Y) := λ f, of_cat.map f
| X (prod Y Z) := λ f, prod_mk (transformation f.1) (transformation f.2)
| X (coprod Y Z) := λ f, f.elim
  (λ f, (transformation f) ≫ inl)
  (λ f, (transformation f) ≫ inr)

lemma transformation_eq_of_syntax_transformation_syntax {X : C} {Y : prod_coprod C}
  (x : (to_presheaf.obj Y).obj (opposite.op X)) :
  transformation x = of_syntax (transformation_syntax x) :=
by induction Y; simp [transformation, transformation_syntax, *]; tidy

lemma transformation_lemma : Π {X Y : prod_coprod C}
  (f : X ⟶ Y) ⦃Z : C⦄ (z : (to_presheaf.obj X).obj (op Z)),
  transformation ((to_presheaf.map f).app (op Z) z) =
  transformation z ≫ f :=
begin
  intros X Y f Z z, revert Z z,
  refine hom_induction f _ _ _ _ _ _ _ _ _; intros; try { ext };
  try { dsimp at * }; try { simp * at * },
  cases z; simp *
end

def transformation_inverse {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) :
  (to_presheaf.obj Y).obj (opposite.op X) :=
yoneda_equiv (to_presheaf.map f)

lemma transformation_transformation_inverse {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) : transformation (transformation_inverse f) = f :=
begin
  simp [yoneda_equiv, transformation_inverse, transformation_lemma],
  exact category.id_comp _,
end

lemma transformation_inverse_transformation {X : C} {Y : prod_coprod C}
  (f : (to_presheaf.obj Y).obj (opposite.op X)) :
  transformation_inverse (transformation f) = f :=
begin
  simp [yoneda_equiv, transformation_inverse, transformation_lemma],
  induction Y,
  { simp [transformation], exact category.id_comp _ },
  { simp [transformation, *] },
  { cases f;
    simp [transformation, *] }
end

instance of_cat_full : full (@of_cat C _) :=
{ preimage := λ X Y f, ((to_presheaf.map f).app (op X) (𝟙 X)),
  witness' := λ X Y f, begin
    have := transformation_lemma f (𝟙 X),
    simp at this,
    erw [category.id_comp] at this,
    simpa using this
  end }

instance of_cat_faithful : faithful (@of_cat C _) :=
{ map_injective' := λ X Y f g h, begin
    have := congr_arg transformation_inverse h,
    simp [transformation_inverse] at this,
    erw [category.id_comp] at this,
    erw [category.id_comp] at this,
    assumption
end }

def normalize {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) : hom_syntax (of_cat' X) Y :=
transformation_syntax (transformation_inverse f)

lemma of_syntax_normalize {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) : of_syntax (normalize f) = f :=
by rw [normalize, ← transformation_eq_of_syntax_transformation_syntax,
  transformation_transformation_inverse]

end prod_coprod