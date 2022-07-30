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

inductive syntax : Π (X Y : prod_coprod C), Type
| of_cat {X Y : C} : (X ⟶ Y) → syntax (of_cat' X) (of_cat' Y)
| prod_mk {X Y Z : prod_coprod C} : syntax X Y → syntax X Z → syntax X (Y.prod Z)
| fst {X Y : prod_coprod C} : syntax (X.prod Y) X
| snd {X Y : prod_coprod C} : syntax (X.prod Y) Y
| coprod_mk {X Y Z : prod_coprod C} : syntax X Z → syntax Y Z → syntax (X.coprod Y) Z
| inl {X Y : prod_coprod C} : syntax X (X.coprod Y)
| inr {X Y : prod_coprod C} : syntax Y (X.coprod Y)
| id (X : prod_coprod C) : syntax X X
| comp {X Y Z : prod_coprod C} : syntax X Y → syntax Y Z → syntax X Z

namespace syntax

inductive rel : Π {X Y : prod_coprod C}, syntax X Y → syntax X Y → Prop
| refl {X Y : prod_coprod C} (f : syntax X Y) : rel f f
| symm {X Y : prod_coprod C} {f g : syntax X Y} : rel f g → rel g f
| trans {X Y : prod_coprod C} {f g h : syntax X Y} : rel f g → rel g h → rel f h
| comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : syntax X Y} {g₁ g₂ : syntax Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp g₁) (f₂.comp g₂)
| prod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : syntax X Y} {g₁ g₂ : syntax X Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.prod_mk g₁) (f₂.prod_mk g₂)
| coprod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : syntax X Z} {g₁ g₂ : syntax Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.coprod_mk g₁) (f₂.coprod_mk g₂)
| id_comp {X Y : prod_coprod C} (f : syntax X Y) : rel ((syntax.id X).comp f) f
| comp_id {X Y : prod_coprod C} (f : syntax X Y) : rel (f.comp (syntax.id Y)) f
| assoc {W X Y Z : prod_coprod C} (f : syntax W X) (g : syntax X Y) (h : syntax Y Z) :
  rel ((f.comp g).comp h) (f.comp (g.comp h))
| of_cat_id {X : C} : rel (syntax.of_cat (𝟙 X)) (syntax.id (of_cat' X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  rel (syntax.of_cat (f ≫ g)) (syntax.comp (syntax.of_cat f) (syntax.of_cat g))
| mk_comp_fst {X Y Z : prod_coprod C} (f : syntax X Y) (g : syntax X Z) :
  rel (syntax.comp (syntax.prod_mk f g) syntax.fst) f
| mk_comp_snd {X Y Z : prod_coprod C} (f : syntax X Y) (g : syntax X Z) :
  rel (syntax.comp (syntax.prod_mk f g) syntax.snd) g
| prod_eta {X Y Z : prod_coprod C} (f : syntax X (Y.prod Z)) :
  rel (syntax.prod_mk (f.comp syntax.fst) (f.comp syntax.snd)) f
| inl_comp_mk {X Y Z : prod_coprod C} (f : syntax X Z) (g : syntax Y Z) :
  rel (syntax.comp syntax.inl (syntax.coprod_mk f g)) f
| inr_comp_mk {X Y Z : prod_coprod C} (f : syntax X Z) (g : syntax Y Z) :
  rel (syntax.comp syntax.inr (syntax.coprod_mk f g)) g
| coprod_eta {X Y Z : prod_coprod C} (f : syntax (X.coprod Y) Z) :
  rel (syntax.coprod_mk (syntax.inl.comp f) (syntax.inr.comp f)) f

attribute [refl] rel.refl
attribute [symm] rel.symm
attribute [trans] rel.trans

infixl ` ♥ `: 50 := rel

lemma rel_prod {X Y Z : prod_coprod C} {f g : syntax X (Y.prod Z)}
  (h₁ : rel (f.comp syntax.fst) (g.comp syntax.fst))
  (h₂ : rel (f.comp syntax.snd) (g.comp syntax.snd)) :
  rel f g :=
calc f ♥ syntax.prod_mk (f.comp syntax.fst) (f.comp syntax.snd) : rel.symm (rel.prod_eta f)
   ... ♥ syntax.prod_mk (g.comp syntax.fst) (g.comp syntax.snd) : rel.prod_mk_congr h₁ h₂
   ... ♥ g : rel.prod_eta g

lemma rel_coprod {X Y Z : prod_coprod C} {f g : syntax (X.coprod Y) Z}
  (h₁ : rel (syntax.inl.comp f) (syntax.inl.comp g))
  (h₂ : rel (syntax.inr.comp f) (syntax.inr.comp g)) :
  rel f g :=
calc f ♥ syntax.coprod_mk (syntax.inl.comp f) (syntax.inr.comp f) : rel.symm (rel.coprod_eta f)
   ... ♥ syntax.coprod_mk (syntax.inl.comp g) (syntax.inr.comp g) : rel.coprod_mk_congr h₁ h₂
   ... ♥ g : rel.coprod_eta g

instance rel_setoid (X Y : prod_coprod C) : setoid (syntax X Y) :=
{ r := rel,
  iseqv := ⟨rel.refl, λ _ _, rel.symm, λ _ _ _, rel.trans⟩ }

end syntax

section syntax

open syntax

def hom (X Y : prod_coprod C) : Type := quotient (syntax.rel_setoid X Y)

instance : category_struct (prod_coprod C) :=
{ hom := hom,
  id := λ X, quotient.mk' (syntax.id X),
  comp := λ X Y Z f g, quotient.lift_on₂ f g (λ f g, quotient.mk' (syntax.comp f g))
    (λ f₁ g₁ f₂ g₂ hf hg, quotient.sound (rel.comp_congr hf hg)) }

instance : category (prod_coprod C) :=
{ id_comp' := λ X Y f, quotient.induction_on f (λ f, quotient.sound (rel.id_comp f)),
  comp_id' := λ X Y f, quotient.induction_on f (λ f, quotient.sound (rel.comp_id f)),
  assoc' := λ W X Y Z f g h, quotient.induction_on₃ f g h
    (λ f g h, quotient.sound (rel.assoc f g h)) }

def of_syntax {X Y : prod_coprod C} : syntax X Y → (X ⟶ Y) := quotient.mk

def of_cat : C ⥤ prod_coprod C :=
{ obj := λ X, of_cat' X,
  map := λ X Y f, of_syntax (syntax.of_cat f),
  map_id' := λ X, quotient.sound rel.of_cat_id,
  map_comp' := λ X Y Z f g, quotient.sound (rel.of_cat_comp f g) }

@[simp] lemma of_cat_obj (X : C) : of_cat.obj X = of_cat' X := rfl

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
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.mk_comp_fst _ _))

@[simp] lemma prod_mk_comp_snd {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ snd = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.mk_comp_snd _ _))

lemma prod_mk_eta {X Y Z : prod_coprod C} (f : X ⟶ Y.prod Z) :
  prod_mk (f ≫ fst) (f ≫ snd) = f :=
quotient.induction_on f (λ f, quotient.sound (syntax.rel.prod_eta _))

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
    apply syntax.rec_on f; try { assumption },
    { intros _ _ _ f g,
      exact h₂ (of_syntax f) (of_syntax g) },
    { intros _ _ _ f g,
      exact h₅ (of_syntax f) (of_syntax g) },
    { intros _ _ _ f g,
      exact h₉ (of_syntax f) (of_syntax g) }
  end

@[simp] lemma inl_comp_coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inl ≫ coprod_mk f g = f :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.inl_comp_mk _ _))

@[simp] lemma inr_comp_coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inr ≫ coprod_mk f g = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.inr_comp_mk _ _))

lemma coprod_mk_eta {X Y Z : prod_coprod C} (f : X.coprod Y ⟶ Z) :
  coprod_mk (inl ≫ f) (inr ≫ f) = f :=
quotient.induction_on f (λ f, quotient.sound (syntax.rel.coprod_eta _))

@[ext] lemma coprod_hom_ext {X Y Z : prod_coprod C} {f g : X.coprod Y ⟶ Z}
  (h₁ : inl ≫ f = inl ≫ g ) (h₂ : inr ≫ f = inr ≫ g) : f = g :=
begin
  conv_lhs { rw ← coprod_mk_eta f },
  rw [h₁, h₂, coprod_mk_eta]
end

def wf_rel (x y : (prod_coprod C × prod_coprod C) ⊕
  (prod_coprod C × prod_coprod C × prod_coprod C)) :Prop :=
sum.lex (measure sizeof) (measure sizeof) x y



@[simp] def sizeof2 : prod_coprod C → ℕ
| (of_cat' X) := 0
| (prod X Y) := sizeof2 X + sizeof2 Y + 0
| (coprod X Y) := sizeof2 X + sizeof2 Y + 1

def hwf_rel_wf : has_well_founded ((prod_coprod C × prod_coprod C) ⊕
  (prod_coprod C × prod_coprod C × prod_coprod C)) :=
⟨_, measure_wf (λ x, sum.cases_on x
    (λ x, sizeof x.1 + sizeof x.2)
    (λ x, sizeof x.1 + sizeof x.2.1 + sizeof x.2.2))⟩

@[simp] lemma hwf_rel_wf_simp :@has_well_founded.r _ (@hwf_rel_wf C _) =
  measure (λ x, sum.cases_on x
    (λ x, sizeof x.1 + sizeof x.2)
    (λ x, sizeof x.1 + sizeof x.2.1 + sizeof x.2.2)) := rfl

meta def wf_dec_tac : tactic unit :=
`[try { simp },
  well_founded_tactics.default_dec_tac]

/-- Defining two maps by mutual induction. Morally we are defining the following.
  First - `norm_type (X Y : prod_coprod C) : Type`
    The type of normal form of maps `X ⟶ Y`.
  Second - `norm_type_not_proj (X Y Z : prod_coprod C) : Type`
    The type of normal forms of maps `(X.prod Y) ⟶ Z` that cannot be written
    `fst ≫ f` or `snd ≫ f` for any `f`
-/
@[simp] def norm_type :
  ((prod_coprod C × prod_coprod C) ⊕
  (prod_coprod C × prod_coprod C × prod_coprod C)) → Type
| (sum.inl (X, prod Y Z)) := norm_type (sum.inl (X, Y)) × norm_type (sum.inl (X, Z))
| (sum.inl (of_cat' X, coprod Y Z)) :=
  norm_type (sum.inl (of_cat' X, Y)) ⊕ norm_type (sum.inl (of_cat' X, Z))
| (sum.inl (of_cat' X, of_cat' Y)) := X ⟶ Y
| (sum.inl (coprod X Y, Z)) := norm_type (sum.inl (X, Z)) × norm_type (sum.inl (Y, Z))
| (sum.inl (prod X Y, of_cat' Z)) :=
  norm_type (sum.inl (X, of_cat' Z)) ⊕ norm_type (sum.inl (X, of_cat' Z))
| (sum.inl (prod X Y, Z)) :=
  norm_type (sum.inl (X, Z)) ⊕ -- fst ≫ (f : X ⟶  Z)
  norm_type (sum.inl (Y, Z)) ⊕ -- snd ≫ (f : Y ⟶ Z)
  norm_type (sum.inr (X, Y, Z))
| (sum.inr (W, X, coprod Y Z)) :=
  norm_type (sum.inr (W, X, Y)) ⊕  -- (f : prod W X ⟶ Y) ≫ inl
  norm_type (sum.inr (W, X, Z))  -- (f : prod W X ⟶ Z) ≫ inr
| (sum.inr (W, X, prod Y Z)) :=
  (norm_type (sum.inr (W, X, Y)) × norm_type (sum.inr (W, X, Z))) ⊕ -- prod_mk _ _
  (norm_type (sum.inl (W, Y)) × norm_type (sum.inl (X, Z))) ⊕
  (norm_type (sum.inl (W, Z)) × norm_type (sum.inl (X, Y)))
| (sum.inr (X, Y, of_cat' Z)) := empty
using_well_founded {
  dec_tac := wf_dec_tac,
  rel_tac := λ _ _, `[exact hwf_rel_wf] }

variables {W X Y Z : prod_coprod C}

@[simp] lemma norm_type_inl_prod_right : norm_type (sum.inl (X, prod Y Z)) =
  (norm_type (sum.inl (X, Y)) × norm_type (sum.inl (X, Z))) :=
by cases X; simp

@[simp] lemma norm_type_inl_prod_left : norm_type (sum.inl (prod X Y, Z)) =
  (norm_type (sum.inl (X, Z)) ⊕ norm_type (sum.inl (Y, Z)) ⊕
  norm_type (sum.inr (X, Y, Z))) :=
by induction Z; simp *

@[simp] def to_presheaf_syntax :
  Π (f : (Σ (X Y : prod_coprod C), syntax X Y) ⊕
  (Σ (X Y Z : prod_coprod C),
    { f : syntax (X.prod Y) Z //
      (∀ g, of_syntax f ≠ fst ≫ g) ∧
      (∀ g, of_syntax f ≠ snd ≫ g) } )),
  (show Type, from sum.cases_on f
    (λ f, norm_type (sum.inl (f.1, f.2.1)))
    (λ f, norm_type (sum.inr (f.1, f.2.1, f.2.2.1))))
| (sum.inl ⟨_, _, syntax.of_cat f⟩) := by simp; exact f
| (sum.inl ⟨X, _, @syntax.prod_mk _ _ _ Y Z f g⟩) := by
  simp; exact (to_presheaf_syntax (sum.inl ⟨_, _, f⟩), to_presheaf_syntax (sum.inl ⟨_, _, g⟩))
| (sum.inl ⟨_, _, syntax.fst⟩) := begin simp, end
#exit
lemma to_presheaf_syntax_comp {X Y Z : prod_coprod C} (f : syntax X Y) (g : syntax Y Z) :
  to_presheaf_syntax (f.comp g) = to_presheaf_syntax f ≫ to_presheaf_syntax g := rfl

lemma to_presheaf_syntax_rel {X Y : prod_coprod C} (f g : syntax X Y) (h : rel f g) :
  to_presheaf_syntax f = to_presheaf_syntax g :=
begin
  induction h; try { simp * }; try { ext }; try { refl }; tidy,
end

def to_presheaf : prod_coprod C ⥤ (Cᵒᵖ ⥤ Type) :=
{ obj := to_presheaf_obj,
  map := λ X Y f, quotient.lift_on f (to_presheaf_syntax) to_presheaf_syntax_rel,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ f g, quotient.induction_on₂ f g begin intros, simp,
    erw quotient.lift_on_mk,
    simp [to_presheaf_syntax_comp] end }

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

end syntax

def transformation_syntax : Π {X : C} {Y : prod_coprod C}, (to_presheaf.obj Y).obj (opposite.op X) →
  syntax (of_cat' X) Y
| X (of_cat' Y) := λ f, syntax.of_cat f
| X (prod Y Z) := λ f, syntax.prod_mk (transformation_syntax f.1) (transformation_syntax f.2)
| X (coprod Y Z) := λ f, f.elim
  (λ f, (transformation_syntax f).comp syntax.inl)
  (λ f, (transformation_syntax f).comp syntax.inr)

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

lemma transformation_left_naturality : Π {X Y : prod_coprod C}
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
  simp [yoneda_equiv, transformation_inverse, transformation_left_naturality],
  exact category.id_comp _,
end

lemma transformation_inverse_transformation {X : C} {Y : prod_coprod C}
  (f : (to_presheaf.obj Y).obj (opposite.op X)) :
  transformation_inverse (transformation f) = f :=
begin
  simp [yoneda_equiv, transformation_inverse, transformation_left_naturality],
  induction Y,
  { simp [transformation], exact category.id_comp _ },
  { simp [transformation, *] },
  { cases f;
    simp [transformation, *] }
end

instance of_cat_full : full (@of_cat C _) :=
{ preimage := λ X Y f, ((to_presheaf.map f).app (op X) (𝟙 X)),
  witness' := λ X Y f, begin
    have := transformation_left_naturality f (𝟙 X),
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
  (f : (of_cat' X) ⟶ Y) : syntax (of_cat' X) Y :=
transformation_syntax (transformation_inverse f)

lemma of_syntax_normalize {X : C} {Y : prod_coprod C}
  (f : (of_cat' X) ⟶ Y) : of_syntax (normalize f) = f :=
by rw [normalize, ← transformation_eq_of_syntax_transformation_syntax,
  transformation_transformation_inverse]

end prod_coprod