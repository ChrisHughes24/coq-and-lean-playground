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
| mk_fst_comp {X Y Z : prod_coprod C} (f : syntax X Y) (g : syntax X Z) :
  rel (syntax.comp (syntax.prod_mk f g) syntax.fst) f
| mk_snd_comp {X Y Z : prod_coprod C} (f : syntax X Y) (g : syntax X Z) :
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

@[simp] lemma prod_mk_fst_comp {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ fst = f :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.mk_fst_comp _ _))

@[simp] lemma prod_mk_snd_comp {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ snd = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (syntax.rel.mk_snd_comp _ _))

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

inductive list_proj : Π (X Y : prod_coprod C), Type -- Y is not prod
| empty {X : prod_coprod C} : list_proj X X
| fst_comp {X Y Z : prod_coprod C} (f : list_proj X Z) : list_proj (prod X Y) Z
| snd_comp {X Y Z : prod_coprod C} (f : list_proj Y Z) : list_proj (prod X Y) Z

inductive list_inj : Π (X Y : prod_coprod C), Type -- X is not coprod
| empty {X : prod_coprod C} : list_inj X X
| comp_inl {X Y Z : prod_coprod C} (f : list_inj X Y) : list_inj X (coprod Y Z)
| comp_inr {X Y Z : prod_coprod C} (f : list_inj X Z) : list_inj X (coprod Y Z)

inductive norm_hom : prod_coprod C → prod_coprod C → Type
| prod_mk_of_cat {W : C} {X Y Z : prod_coprod C}
  (f : norm_hom (of_cat' W) X) (g : norm_hom (of_cat' W) Y)
  (h : list_inj (prod X Y) Z) :
  norm_hom (of_cat' W) Z
| prod_mk_prod {V W X Y Z : prod_coprod C}
  (f : norm_hom (prod V W) X) (g : norm_hom (prod V W) Y)
  (h : list_inj (prod X Y) Z) :
  norm_hom (prod V W) Z
| coprod_mk_of_cat {W X Y : prod_coprod C} {Z : C}
  (f : list_proj W (coprod X Y))
  (g : norm_hom X (of_cat' Z)) (h : norm_hom Y (of_cat' Z)) :
  norm_hom W (of_cat' Z)
| coprod_mk_coprod {V W X Y Z : prod_coprod C}
  (f : list_proj V (coprod W X))
  (g : norm_hom W (coprod Y Z)) (h : norm_hom X (coprod Y Z)) :
  norm_hom V (coprod Y Z)
| prod_mk_coprod {W X Y Z : prod_coprod C}
  (f : norm_hom (coprod W X) Y) (g : norm_hom (coprod W X) Z) :
  norm_hom (coprod W X) (prod Y Z)
| of_cat {W : prod_coprod C} {X Y : C} {Z : prod_coprod C}
  (f : list_proj W (of_cat' X)) (g : X ⟶ Y)
  (h : list_inj (of_cat' Y) Z) : norm_hom W Z

namespace norm_hom

open list_inj list_proj

def prod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z),
  norm_hom X (prod Y Z)
| (of_cat' _) _ _ f g := prod_mk_of_cat f g empty
| (coprod _ _) _ _ f g := prod_mk_coprod f g
| (prod _ _) _ _ f g := prod_mk_prod f g empty

def comp_fst : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)), norm_hom X Y
| _ _ _ (@prod_mk_of_cat _ _ W X Y Z f g empty) := f
| A B D (@prod_mk_prod _ _ V W X Y Z f g empty) := f
| A B D (@prod_mk_coprod _ _ W X Y Z f g) := f

@[simp] lemma comp_fst_prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
  comp_fst (prod_mk f g) = f :=
by cases X; simp [comp_fst, prod_mk]

def comp_snd : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)), norm_hom X Z
| _ _ _ (@prod_mk_of_cat _ _ W X Y Z f g empty) := g
| A B D (@prod_mk_prod _ _ V W X Y Z f g empty) := g
| A B D (@prod_mk_coprod _ _ W X Y Z f g) := g

@[simp] lemma comp_snd_prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
  comp_snd (prod_mk f g) = g :=
by cases X; simp [comp_snd, prod_mk]

lemma prod_eta : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)),
  prod_mk (comp_fst f) (comp_snd f) = f
| _ _ _ (prod_mk_of_cat f g empty) := rfl
| _ _ _ (prod_mk_prod f g empty) := rfl
| _ _ _ (prod_mk_coprod f g) := rfl

def coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
  norm_hom (coprod X Y) Z
| _ _ (of_cat' _) f g := coprod_mk_of_cat empty f g
| _ _ (coprod _ _) f g := coprod_mk_coprod empty f g
| _ _ (prod _ _) f g := prod_mk_coprod
  (coprod_mk (comp_fst f) (comp_fst g))
  (coprod_mk (comp_snd f) (comp_snd g))

lemma coprod_mk_comp_fst : Π {W X Y Z : prod_coprod C}
  (f : norm_hom W (prod Y Z)) (g : norm_hom X (prod Y Z)),
  comp_fst (coprod_mk f g) = coprod_mk (comp_fst f) (comp_fst g) :=
begin
  intros,
  cases Y;
  dsimp [coprod_mk, comp_fst]; refl
end

lemma coprod_mk_comp_snd : Π {W X Y Z : prod_coprod C}
  (f : norm_hom W (prod Y Z)) (g : norm_hom X (prod Y Z)),
  comp_snd (coprod_mk f g) = coprod_mk (comp_snd f) (comp_snd g) :=
begin
  intros,
  cases Y;
  dsimp [coprod_mk, comp_fst]; refl
end

def inl_comp : Π {X Y Z : prod_coprod C}, norm_hom (coprod X Y) Z → norm_hom X Z
| _ _ _ (coprod_mk_of_cat empty g h) := g
| _ _ _ (coprod_mk_coprod empty g h) := g
| _ _ _ (@prod_mk_coprod _ _ W X Y Z f g) := prod_mk (inl_comp f) (inl_comp g)

def inr_comp : Π {X Y Z : prod_coprod C}, norm_hom (coprod X Y) Z → norm_hom Y Z
| _ _ _ (coprod_mk_of_cat empty g h) := h
| _ _ _ (coprod_mk_coprod empty g h) := h
| _ _ _ (@prod_mk_coprod _ _ W X Y Z f g) := prod_mk (inr_comp f) (inr_comp g)

lemma inl_comp_comp_fst : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
  inl_comp (comp_fst f) = comp_fst (inl_comp f)
| A B D _ (prod_mk_coprod f g) := by simp [comp_fst, inl_comp]

lemma inr_comp_comp_fst : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
  inr_comp (comp_fst f) = comp_fst (inr_comp f)
| A B D _ (prod_mk_coprod f g) := by simp [comp_fst, inr_comp]

lemma inl_comp_comp_snd : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
  inl_comp (comp_snd f) = comp_snd (inl_comp f)
| A B D _ (prod_mk_coprod f g) := by simp [comp_snd, inl_comp]

lemma inr_comp_comp_snd : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
  inr_comp (comp_snd f) = comp_snd (inr_comp f)
| A B D _ (prod_mk_coprod f g) := by simp [comp_snd, inr_comp]

@[simp] lemma inl_comp_coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
  inl_comp (coprod_mk f g) = f
| _ _ (of_cat' Z) _ _ := rfl
| _ _ (coprod Y Z) _ _ := rfl
| _ _ (prod Y Z) f g :=
by rw [coprod_mk, inl_comp, inl_comp_coprod_mk, inl_comp_coprod_mk, prod_eta]

@[simp] lemma inr_comp_coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
  inr_comp (coprod_mk f g) = g
| _ _ (of_cat' Z) _ _ := rfl
| _ _ (coprod Y Z) _ _ := rfl
| _ _ (prod Y Z) f g :=
by rw [coprod_mk, inr_comp, inr_comp_coprod_mk, inr_comp_coprod_mk, prod_eta]

lemma coprod_eta : Π {X Y Z : prod_coprod C} (f : norm_hom (coprod X Y) Z),
  coprod_mk (inl_comp f) (inr_comp f) = f
| _ _ _ (coprod_mk_of_cat empty g h) := rfl
| _ _ _ (coprod_mk_coprod empty g h) := rfl
| _ _ _ (prod_mk_coprod f g) :=
  by simp [coprod_mk, inl_comp, inr_comp, coprod_eta f, coprod_eta g]

def prod_mk_l : Π {W X Y Z : prod_coprod C} (f : norm_hom W X) (g : norm_hom W Y)
  (h : list_inj (prod X Y) Z), norm_hom W Z
| (of_cat' _) _ _ _ f g h := prod_mk_of_cat f g h
| (coprod V W) X Y Z f g h :=
  coprod_mk
    (prod_mk_l (inl_comp f) (inl_comp g) h)
    (prod_mk_l (inr_comp f) (inr_comp g) h)
| (prod _ _) _ _ _ f g h := prod_mk_prod f g h

def coprod_mk_l : Π {W X Y Z : prod_coprod C} (f : list_proj W (coprod X Y))
  (g : norm_hom X Z) (h : norm_hom Y Z), norm_hom W Z
| _ _ _ (of_cat' _) f g h := coprod_mk_of_cat f g h
| X Y Z (prod V W) f g h :=
  prod_mk
    (coprod_mk_l f (comp_fst g) (comp_fst h))
    (coprod_mk_l f (comp_snd g) (comp_snd h))
| _ _ _ (coprod _ _) f g h := coprod_mk_coprod f g h

def fst_comp : Π {X Y Z : prod_coprod C}
  (f : norm_hom X Z), norm_hom (prod X Y) Z
| _ _ _ (prod_mk_of_cat f g h) :=
  prod_mk_l (fst_comp f) (fst_comp g) h
| _ _ _ (prod_mk_prod f g h) :=
  prod_mk_l (fst_comp f) (fst_comp g) h
| _ _ _ (prod_mk_coprod f g) :=
  prod_mk (fst_comp f) (fst_comp g)
| _ _ _ (coprod_mk_of_cat f g h) := coprod_mk_of_cat f.fst_comp g h
| _ _ _ (coprod_mk_coprod f g h) := coprod_mk_coprod f.fst_comp g h
| _ _ _ (of_cat f g h) := of_cat f.fst_comp g h

def snd_comp : Π {X Y Z : prod_coprod C}
  (f : norm_hom Y Z), norm_hom (prod X Y) Z
| _ _ _ (prod_mk_of_cat f g h) :=
  prod_mk_l (snd_comp f) (snd_comp g) h
| _ _ _ (prod_mk_prod f g h) :=
  prod_mk_l (snd_comp f) (snd_comp g) h
| _ _ _ (prod_mk_coprod f g) :=
  prod_mk (snd_comp f) (snd_comp g)
| _ _ _ (coprod_mk_of_cat f g h) := coprod_mk_of_cat f.snd_comp g h
| _ _ _ (coprod_mk_coprod f g h) := coprod_mk_coprod f.snd_comp g h
| _ _ _ (of_cat f g h) := of_cat f.snd_comp g h

def list_proj_comp {X Y Z : prod_coprod C} (f : list_proj X Y) : Π (g : norm_hom Y Z),
  norm_hom X Z :=
list_proj.rec_on f (λ _, id) (λ _ _ _ f ih g, fst_comp (ih g)) (λ _ _ _ f ih g, snd_comp (ih g))

@[simp] lemma list_proj_comp_empty {X Y : prod_coprod C} (f : norm_hom X Y) :
  list_proj_comp list_proj.empty f = f := rfl

@[simp] lemma list_proj_comp_fst_comp {W X Y Z : prod_coprod C} (f : list_proj W Y) (g : norm_hom Y Z) :
  list_proj_comp (list_proj.fst_comp f : list_proj (prod W X) Y) g = fst_comp (list_proj_comp f g) := rfl

@[simp] lemma list_proj_comp_snd_comp {W X Y Z : prod_coprod C} (f : list_proj X Y) (g : norm_hom Y Z) :
  list_proj_comp (list_proj.snd_comp f : list_proj (prod W X) Y) g = snd_comp (list_proj_comp f g) := rfl

@[simp] lemma list_proj_comp_coprod_mk_of_cat : Π {W X Y : prod_coprod C} {Z : C}
  (f : list_proj W (coprod X Y))
  (g : norm_hom X (of_cat' Z)) (h : norm_hom Y (of_cat' Z)),
  list_proj_comp f (coprod_mk_of_cat empty g h) = coprod_mk_of_cat f g h
| _ _ _ _ list_proj.empty _ _ := rfl
| _ _ _ _ (list_proj.fst_comp f) g h := by rw [list_proj_comp_fst_comp, list_proj_comp_coprod_mk_of_cat, fst_comp]
| _ _ _ _ (list_proj.snd_comp f) g h := by rw [list_proj_comp_snd_comp, list_proj_comp_coprod_mk_of_cat, snd_comp]

@[simp] lemma list_proj_comp_coprod_mk_coprod : Π {V W X Y Z : prod_coprod C}
  (f : list_proj V (coprod W X))
  (g : norm_hom W (coprod Y Z)) (h : norm_hom X (coprod Y Z)),
  list_proj_comp f (coprod_mk_coprod empty g h) = coprod_mk_coprod f g h
| _ _ _ _ _ list_proj.empty _ _ := rfl
| _ _ _ _ _ (list_proj.fst_comp f) g h := by rw [list_proj_comp_fst_comp, list_proj_comp_coprod_mk_coprod, fst_comp]
| _ _ _ _ _ (list_proj.snd_comp f) g h := by rw [list_proj_comp_snd_comp, list_proj_comp_coprod_mk_coprod, snd_comp]

@[simp] lemma list_proj_comp_of_cat : Π {W : prod_coprod C} {X Y : C} {Z : prod_coprod C}
  (f : list_proj W (of_cat' X)) (g : X ⟶ Y)
  (h : list_inj (of_cat' Y) Z),
  list_proj_comp f (of_cat empty g h) = of_cat f g h
| _ _ _ _ list_proj.empty _ _ := rfl
| _ _ _ _ (list_proj.fst_comp f) g h := by rw [list_proj_comp_fst_comp, list_proj_comp_of_cat, fst_comp]
| _ _ _ _ (list_proj.snd_comp f) g h := by rw [list_proj_comp_snd_comp, list_proj_comp_of_cat, snd_comp]

set_option eqn_compiler.lemmas false

def comp_list_proj : Π {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : list_proj Y Z),
  norm_hom X Z
| _ _ _ f empty := f
| _ _ _ f (list_proj.fst_comp g) := comp_list_proj (comp_fst f) g
| _ _ _ f (list_proj.snd_comp g) := comp_list_proj (comp_snd f) g

set_option eqn_compiler.lemmas true

def comp_inl : Π {X Y Z : prod_coprod C}
  (f : norm_hom X Y), norm_hom X (coprod Y Z)
| _ _ _ (coprod_mk_of_cat f g h) :=
  coprod_mk_l f (comp_inl g) (comp_inl h)
| _ _ _ (coprod_mk_coprod f g h) :=
  coprod_mk_l f (comp_inl g) (comp_inl h)
| _ _ _ (prod_mk_of_cat f g h) := prod_mk_of_cat f g h.comp_inl
| _ _ _ (prod_mk_prod f g h) := prod_mk_prod f g h.comp_inl
| _ _ A (prod_mk_coprod f g) :=
  prod_mk_l f g list_inj.empty.comp_inl
| _ _ _ (of_cat f g h) := of_cat f g h.comp_inl

def comp_inr : Π {X Y Z : prod_coprod C}
  (f : norm_hom X Z), norm_hom X (coprod Y Z)
| _ _ _ (coprod_mk_of_cat f g h) :=
  coprod_mk_l f (comp_inr g) (comp_inr h)
| _ _ _ (coprod_mk_coprod f g h) :=
  coprod_mk_l f (comp_inr g) (comp_inr h)
| _ _ _ (prod_mk_of_cat f g h) := prod_mk_of_cat f g h.comp_inr
| _ _ _ (prod_mk_prod f g h) := prod_mk_prod f g h.comp_inr
| _ _ A (prod_mk_coprod f g) :=
  prod_mk_l f g list_inj.empty.comp_inr
| _ _ _ (of_cat f g h) := of_cat f g h.comp_inr

protected def id : Π (X : prod_coprod C), norm_hom X X
| (of_cat' X) := of_cat empty (𝟙 X) empty
| (prod X Y) := prod_mk (fst_comp (id X)) (snd_comp (id Y))
| (coprod X Y) := coprod_mk (comp_inl (id X)) (comp_inr (id Y))

set_option eqn_compiler.lemmas false

def comp_list_inj {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : list_inj Y Z) :
  norm_hom X Z :=
list_inj.rec_on g (λ _, id) (λ _ _ _ g ih f, comp_inl (ih f)) (λ _ _ _ g ih f, comp_inr (ih f)) f

@[simp] lemma comp_list_inj_empty {X Y : prod_coprod C} (f : norm_hom X Y) :
  comp_list_inj f list_inj.empty = f := rfl

@[simp] lemma comp_list_inj_comp_inl {W X Y Z : prod_coprod C} (f : norm_hom W X) (g : list_inj X Y) :
  comp_list_inj f (list_inj.comp_inl g : list_inj X (coprod Y Z)) = comp_inl (comp_list_inj f g) := rfl

@[simp] lemma comp_list_inj_comp_inr {W X Y Z : prod_coprod C} (f : norm_hom W X) (g : list_inj X Z) :
  comp_list_inj f (list_inj.comp_inr g : list_inj X (coprod Y Z)) = comp_inr (comp_list_inj f g) := rfl

@[simp] lemma comp_list_inj_prod_mk_of_cat : Π {W : C} {X Y Z : prod_coprod C}
  (f : norm_hom (of_cat' W) X) (g : norm_hom (of_cat' W) Y)
  (h : list_inj (prod X Y) Z), comp_list_inj (prod_mk_of_cat f g empty) h = prod_mk_of_cat f g h
| _ _ _ _ _ _ list_inj.empty := rfl
| _ _ _ _ _ _ (list_inj.comp_inl h) := by rw [comp_list_inj_comp_inl, comp_list_inj_prod_mk_of_cat, comp_inl]
| _ _ _ _ _ _ (list_inj.comp_inr h) := by rw [comp_list_inj_comp_inr, comp_list_inj_prod_mk_of_cat, comp_inr]

@[simp] lemma comp_list_inj_prod_mk_prod : Π {V W X Y Z : prod_coprod C}
  (f : norm_hom (prod V W) X) (g : norm_hom (prod V W) Y)
  (h : list_inj (prod X Y) Z),
  comp_list_inj (prod_mk_prod f g empty) h = prod_mk_prod f g h
| _ _ _ _ _ _ _ list_inj.empty := rfl
| _ _ _ _ _ _ _ (list_inj.comp_inl h) := by rw [comp_list_inj_comp_inl, comp_list_inj_prod_mk_prod, comp_inl]
| _ _ _ _ _ _ _ (list_inj.comp_inr h) := by rw [comp_list_inj_comp_inr, comp_list_inj_prod_mk_prod, comp_inr]

@[simp] lemma comp_list_inj_of_cat : Π {W : prod_coprod C} {X Y : C} {Z : prod_coprod C}
  (f : list_proj W (of_cat' X)) (g : X ⟶ Y)
  (h : list_inj (of_cat' Y) Z),
  comp_list_inj (of_cat f g empty) h = of_cat f g h
| _ _ _ _ _ _ list_inj.empty := rfl
| _ _ _ _ _ _ (list_inj.comp_inl h) := by rw [comp_list_inj_comp_inl, comp_list_inj_of_cat, comp_inl]
| _ _ _ _ _ _ (list_inj.comp_inr h) := by rw [comp_list_inj_comp_inr, comp_list_inj_of_cat, comp_inr]

def get_proj_of_cat : Π {X Y : prod_coprod C} {Z : C}
  (f : norm_hom (prod X Y) (of_cat' Z)),
  norm_hom X (of_cat' Z) ⊕ norm_hom Y (of_cat' Z)
| _ _ _ (coprod_mk_of_cat (list_proj.fst_comp f) g h) :=
  sum.inl (coprod_mk_of_cat f g h)
| _ _ _ (coprod_mk_of_cat (list_proj.snd_comp f) g h) :=
  sum.inr (coprod_mk_of_cat f g h)
| _ _ _ (of_cat (list_proj.fst_comp f) g h) :=
  sum.inl (of_cat f g h)
| _ _ _ (of_cat (list_proj.snd_comp f) g h) :=
  sum.inr (of_cat f g h)

def get_inj_of_cat : Π {X : C} {Y Z : prod_coprod C}
  (f : norm_hom (of_cat' X) (coprod Y Z)),
  norm_hom (of_cat' X) Y ⊕ norm_hom (of_cat' X) Z
| _ _ _ (prod_mk_of_cat f g (list_inj.comp_inl h)) :=
  sum.inl (prod_mk_of_cat f g h)
| _ _ _ (prod_mk_of_cat f g (list_inj.comp_inr h)) :=
  sum.inr (prod_mk_of_cat f g h)
| _ _ _ (of_cat f g (list_inj.comp_inl h)) :=
  sum.inl (of_cat f g h)
| _ _ _ (of_cat f g (list_inj.comp_inr h)) :=
  sum.inr (of_cat f g h)


set_option eqn_compiler.lemmas true

-- def comp : Π {X Y Z : prod_coprod C}, norm_hom X Y → norm_hom Y Z → norm_hom X Z
-- | (coprod A B) _ _ f g := coprod_mk (comp (inl_comp f) g) (comp (inr_comp f) g)
-- | _ _ (prod A B) f g := prod_mk (comp f (comp_fst g)) (comp f (comp_snd g))
-- | _ (prod _ _) (of_cat' _) f g :=
--   match get_proj_of_cat g with
--   | sum.inl g := comp (comp_fst f) g
--   | sum.inr g := comp (comp_snd f) g
--   end
-- | (prod _ _) (of_cat' _) _ f g :=
--   match get_proj_of_cat f with
--   | sum.inl f := fst_comp (comp f g)
--   | sum.inr f := snd_comp (comp f g)
--   end
-- | (of_cat' _) (coprod _ _) _ f g :=
--   match get_inj_of_cat f with
--   | sum.inl f := comp f (inl_comp g)
--   | sum.inr f := comp f (inr_comp g)
--   end
-- | _ (of_cat' X) (coprod Y Z) f g :=
--   match get_inj_of_cat g with
--   | sum.inl g := comp_inl (comp f g)
--   | sum.inr g := comp_inr (comp f g)
--   end
-- | (of_cat' _) (of_cat' _) (of_cat' _) (of_cat empty f empty) (of_cat empty g empty) :=
--   of_cat empty (f ≫ g) empty



-- | (prod _ _) _ _ f (prod_mk_prod g h i) :=
--   (prod_mk_prod (comp f g) (comp f h) i)
-- | (prod _ _) _ _ f (prod_mk_of_cat g h i) :=
--   prod_mk_prod (comp f g) (comp f h) i
-- | _ _ _ f (coprod_mk_of_cat g h i) :=
--   coprod_mk_of_cat _ _

--| _ (of_cat' _) _ (of_cat f g empty) (of_cat empty h i) := of_cat f (g ≫ h) i

end norm_hom

inductive norm_hom2 : Π (X Y : prod_coprod C), Type
| of_cat {X Y : C} (f : X ⟶ Y) : norm_hom2 (of_cat' X) (of_cat' Y)
| coprod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Z) (g : norm_hom2 Y Z) :
  norm_hom2 (X.coprod Y) Z
| comp_inl {X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
  norm_hom2 X (coprod Y Z)
| comp_inr {X Y Z : prod_coprod C} (f : norm_hom2 X Z) :
  norm_hom2 X (coprod Y Z)
| prod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 X Z) :
  norm_hom2 X (prod Y Z)
| fst_comp {X Y Z : prod_coprod C} (f : norm_hom2 X Z) :
  norm_hom2 (prod X Y) Z
| snd_comp {X Y Z : prod_coprod C} (f : norm_hom2 Y Z) :
  norm_hom2 (prod X Y) Z

namespace norm_hom2

def list_proj_comp {X Y Z : prod_coprod C} (f : list_proj X Y) : Π (g : norm_hom2 Y Z),
  norm_hom2 X Z :=
list_proj.rec_on f (λ _, id) (λ _ _ _ f ih g, fst_comp (ih g)) (λ _ _ _ f ih g, snd_comp (ih g))

@[simp] lemma list_proj_comp_empty {X Y : prod_coprod C} (f : norm_hom2 X Y) :
  list_proj_comp list_proj.empty f = f := rfl

@[simp] lemma list_proj_comp_fst_comp {W X Y Z : prod_coprod C} (f : list_proj W Y) (g : norm_hom2 Y Z) :
  list_proj_comp (list_proj.fst_comp f : list_proj (prod W X) Y) g = fst_comp (list_proj_comp f g) := rfl

@[simp] lemma list_proj_comp_snd_comp {W X Y Z : prod_coprod C} (f : list_proj X Y) (g : norm_hom2 Y Z) :
  list_proj_comp (list_proj.snd_comp f : list_proj (prod W X) Y) g = snd_comp (list_proj_comp f g) := rfl

def comp_list_inj {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : list_inj Y Z) :
  norm_hom2 X Z :=
list_inj.rec_on g (λ _, id) (λ _ _ _ g ih f, comp_inl (ih f)) (λ _ _ _ g ih f, comp_inr (ih f)) f

@[simp] lemma comp_list_inj_empty {X Y : prod_coprod C} (f : norm_hom2 X Y) :
  comp_list_inj f list_inj.empty = f := rfl

@[simp] lemma comp_list_inj_comp_inl {W X Y Z : prod_coprod C} (f : norm_hom2 W X) (g : list_inj X Y) :
  comp_list_inj f (list_inj.comp_inl g : list_inj X (coprod Y Z)) = comp_inl (comp_list_inj f g) := rfl

@[simp] lemma comp_list_inj_comp_inr {W X Y Z : prod_coprod C} (f : norm_hom2 W X) (g : list_inj X Z) :
  comp_list_inj f (list_inj.comp_inr g : list_inj X (coprod Y Z)) = comp_inr (comp_list_inj f g) := rfl

end norm_hom2

@[simp] def norm_hom.to_norm_hom2 : Π {X Y : prod_coprod C} (f : norm_hom X Y), norm_hom2 X Y
| _ _ (norm_hom.of_cat f g h) := (norm_hom2.list_proj_comp f (norm_hom2.of_cat g)).comp_list_inj h
| _ _ (norm_hom.prod_mk_of_cat f g h) :=
  norm_hom2.comp_list_inj (norm_hom2.prod_mk (norm_hom.to_norm_hom2 f) (norm_hom.to_norm_hom2 g)) h
| _ _ (norm_hom.prod_mk_prod f g h) :=
  norm_hom2.comp_list_inj (norm_hom2.prod_mk (norm_hom.to_norm_hom2 f) (norm_hom.to_norm_hom2 g)) h
| _ _ (norm_hom.prod_mk_coprod f g) :=
  norm_hom2.prod_mk (norm_hom.to_norm_hom2 f) (norm_hom.to_norm_hom2 g)
| _ _ (norm_hom.coprod_mk_of_cat f g h) :=
  norm_hom2.list_proj_comp f (norm_hom2.coprod_mk (norm_hom.to_norm_hom2 g) (norm_hom.to_norm_hom2 h))
| _ _ (norm_hom.coprod_mk_coprod f g h) :=
  norm_hom2.list_proj_comp f (norm_hom2.coprod_mk (norm_hom.to_norm_hom2 g) (norm_hom.to_norm_hom2 h))

@[simp] def norm_hom2.to_norm_hom : Π {X Y : prod_coprod C} (f : norm_hom2 X Y), norm_hom X Y
| _ _ (norm_hom2.of_cat f) := norm_hom.of_cat list_proj.empty f list_inj.empty
| _ _ (norm_hom2.comp_inl f) := norm_hom.comp_inl (norm_hom2.to_norm_hom f)
| _ _ (norm_hom2.comp_inr f) := norm_hom.comp_inr (norm_hom2.to_norm_hom f)
| _ _ (norm_hom2.fst_comp f) := norm_hom.fst_comp (norm_hom2.to_norm_hom f)
| _ _ (norm_hom2.snd_comp f) := norm_hom.snd_comp (norm_hom2.to_norm_hom f)
| _ _ (norm_hom2.prod_mk f g) := norm_hom.prod_mk (norm_hom2.to_norm_hom f) (norm_hom2.to_norm_hom g)
| _ _ (norm_hom2.coprod_mk f g) := norm_hom.coprod_mk (norm_hom2.to_norm_hom f) (norm_hom2.to_norm_hom g)

@[simp] lemma to_norm_hom_list_proj_comp {X Y Z : prod_coprod C} (f : list_proj X Y) (g : norm_hom2 Y Z) :
  (norm_hom2.list_proj_comp f g).to_norm_hom = g.to_norm_hom.list_proj_comp f :=
by induction f generalizing g Z; simp *

@[simp] lemma to_norm_hom_comp_list_inj {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : list_inj Y Z) :
  (norm_hom2.comp_list_inj f g).to_norm_hom = f.to_norm_hom.comp_list_inj g :=
by induction g generalizing f X; simp *

@[simp] def norm_hom2.comp : Π {X Y Z : prod_coprod C} (f : norm_hom2 X Y)
  (g : norm_hom2 Y Z), norm_hom2 X Z
| _ _ _ (norm_hom2.coprod_mk f g) h :=
  norm_hom2.coprod_mk (norm_hom2.comp f h) (norm_hom2.comp g h)
| _ _ _ (norm_hom2.fst_comp f) g :=
  norm_hom2.fst_comp (norm_hom2.comp f g)
| _ _ _ (norm_hom2.snd_comp f) g :=
  norm_hom2.snd_comp (norm_hom2.comp f g)
-- | _ _ _ f (norm_hom2.prod_mk g h) :=
--   norm_hom2.prod_mk (norm_hom2.comp f g) (norm_hom2.comp f h)
-- | _ _ _ f (norm_hom2.comp_inl g) :=
--   norm_hom2.comp_inl (norm_hom2.comp f g)
-- | _ _ _ f (norm_hom2.comp_inr g) :=
--   norm_hom2.comp_inr (norm_hom2.comp f g)
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.of_cat g) :=
  norm_hom2.of_cat (f ≫ g)
| _ _ _ (norm_hom2.comp_inl f) (norm_hom2.coprod_mk g h) :=
  norm_hom2.comp f g
| _ _ _ (norm_hom2.comp_inr f) (norm_hom2.coprod_mk g h) :=
  norm_hom2.comp f h
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.fst_comp h) :=
  norm_hom2.comp f h
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.snd_comp h) :=
  norm_hom2.comp g h
--repeated cases
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inl g) :=
  norm_hom2.comp_inl (norm_hom2.comp (norm_hom2.of_cat f) g)
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inr g) :=
  norm_hom2.comp_inr (norm_hom2.comp (norm_hom2.of_cat f) g)
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.prod_mk g h) :=
  norm_hom2.prod_mk (norm_hom2.comp (norm_hom2.of_cat f) g)
    (norm_hom2.comp (norm_hom2.of_cat f) h)
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.comp_inl g) :=
  norm_hom2.comp_inl (norm_hom2.comp f' g)
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.comp_inl g) :=
  norm_hom2.comp_inl (norm_hom2.comp f' g)
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.comp_inr g) :=
  norm_hom2.comp_inr (norm_hom2.comp f' g)
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.comp_inr g) :=
  norm_hom2.comp_inr (norm_hom2.comp f' g)
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.prod_mk g h) :=
  norm_hom2.prod_mk (norm_hom2.comp f' g) (norm_hom2.comp f' h)
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.prod_mk g h) :=
  norm_hom2.prod_mk (norm_hom2.comp f' g) (norm_hom2.comp f' h)
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inl g) :=
  norm_hom2.comp_inl (norm_hom2.comp f g)
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inr g) :=
  norm_hom2.comp_inr (norm_hom2.comp f g)
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.prod_mk g h) :=
  norm_hom2.prod_mk (norm_hom2.comp f g) (norm_hom2.comp f h)

@[simp] def norm_hom2.to_hom : Π {X Y : prod_coprod C} (f : norm_hom2 X Y), (X ⟶ Y)
| _ _ (norm_hom2.of_cat f) := prod_coprod.of_cat.map f
| _ _ (norm_hom2.comp_inl f) := norm_hom2.to_hom f ≫ inl
| _ _ (norm_hom2.comp_inr f) := norm_hom2.to_hom f ≫ inr
| _ _ (norm_hom2.fst_comp f) := fst ≫ norm_hom2.to_hom f
| _ _ (norm_hom2.snd_comp f) := snd ≫ norm_hom2.to_hom f
| _ _ (norm_hom2.prod_mk f g) := prod_coprod.prod_mk (norm_hom2.to_hom f) (norm_hom2.to_hom g)
| _ _ (norm_hom2.coprod_mk f g) := prod_coprod.coprod_mk (norm_hom2.to_hom f) (norm_hom2.to_hom g)

lemma to_norm_hom_to_norm_hom2 {X Y : prod_coprod C} (f : norm_hom X Y) :
  f.to_norm_hom2.to_norm_hom = f :=
by induction f; simp [norm_hom.to_norm_hom2, norm_hom2.to_norm_hom, *,
   norm_hom.prod_mk, norm_hom.coprod_mk]

lemma forall_eq {α : Sort*} (p : Π (a : α), a = a → Prop) (a : α) :
  (∀ (h : a = a), p a h) = p a rfl :=
by simp

@[simp] lemma forall_eq_comp {α β : Sort*} (a b : β) (p : α → a = b → Prop) :
  (∀ (x : α) (h : a = b), p x h) = (∀ (h : a = b) (x : α), p x h) :=
by rw [forall_swap]

@[simp] lemma forall_eq_eq {α : Sort*} (a : α) (p : Π (b : α), a = b → Prop) :
  (∀ (b : α) (h : a = b), p b h) = p a rfl :=
sorry

@[simp] lemma forall_eq_eq₂ {α : Sort*} (a : α) (p : Π (b : α), b = a → Prop) :
  (∀ (b : α) (h : b = a), p b h) = p a rfl :=
sorry

@[simp] lemma forall_eq_eq₃ {α β : Sort*} (a : α) (p : Π (b : α), β → a = b → Prop) :
  (∀ (b : α) (x : β) (h : a = b), p b x h) = ∀ x : β, p a x rfl :=
sorry

@[simp] lemma forall_eq_eq₄ {α β : Sort*} (a : α) (p : Π (b : α), β → b = a → Prop) :
  (∀ (b : α) (x : β) (h : b = a), p b x h) = ∀ x : β, p a x rfl :=
sorry

@[simp] lemma forall_eq_eq₅ {α β γ : Sort*} (a : α) (p : Π (b : α), β → γ → a = b → Prop) :
  (∀ (b : α) (x : β) (y : γ) (h : a = b), p b x y h) = ∀ (x : β) (y : γ), p a x y rfl :=
sorry

@[simp] lemma forall_eq_eq₆ {α β γ : Sort*} (a : α) (p : Π (b : α), β → γ → b = a → Prop) :
  (∀ (b : α) (x : β) (y : γ) (h : b = a), p b x y h) = ∀ (x : β) (y : γ), p a x y rfl :=
sorry

lemma eq_imp {α : Sort*} (p : Prop) (a : α) :
  ((a = a) → p) = p := by simp

lemma norm_hom2.comp_assoc_aux {W X X' Y Y' Z : prod_coprod C} (hX : X' = X) (hY : Y' = Y)
  (f : norm_hom2 W X) (g : norm_hom2 X' Y) (h : norm_hom2 Y' Z) :
  ((f.comp (show norm_hom2 X Y, from eq.rec_on hX g)).comp
    (show norm_hom2 Y Z, from eq.rec_on hY h)).to_norm_hom =
  (f.comp ((show norm_hom2 X Y, from eq.rec_on hX g).comp
    (show norm_hom2 Y Z, from eq.rec_on hY h))).to_norm_hom :=
begin
  revert h, revert Z, revert g, revert hY, revert Y', revert Y, revert hX, revert X',
  induction f; intros X' hX Y Y' hY g; revert Y';
  induction g; cases hX; dsimp; clear hX; intros Y' hY Z h;
  try { revert g_Y }; induction h;
  try { intros _ _ hY; cases hY };
  try { dsimp [norm_hom2.comp, norm_hom2.of_cat] };
  simp * at *,
  --revert hY, revert h Z Y', revert hX, revert g Y X',
  -- induction f;
  -- intros X' Y g; induction g; intro hX; cases hX;
  -- dsimp;
  -- simp [norm_hom2.comp, norm_hom2.to_norm_hom, eq_imp, forall_eq, *] at *;
  -- intros Z h; induction h;
  -- dsimp;
  -- simp [norm_hom2.comp, norm_hom2.to_norm_hom, eq_imp, forall_eq, *] at *,


  --intros Y' Z h; induction h; intro hY; cases hY;
  -- dsimp at *;
  -- simp only [norm_hom2.comp, norm_hom2.to_norm_hom, eq_imp, forall_eq, forall_eq_comp] at *;
  -- try { simp * },
end

-- def comp_fst : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)), norm_hom X Y
-- | _ _ _ (@prod_mk_of_cat _ _ W X Y Z f g empty) := f
-- | A B D (@prod_mk_prod _ _ V W X Y Z f g empty) := f
-- | A B D (@prod_mk_coprod _ _ W X Y Z f g) := f

-- @[simp] lemma comp_fst_prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
--   comp_fst (prod_mk f g) = f :=
-- by cases X; simp [comp_fst, prod_mk]

-- def comp_snd : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)), norm_hom X Z
-- | _ _ _ (@prod_mk_of_cat _ _ W X Y Z f g empty) := g
-- | A B D (@prod_mk_prod _ _ V W X Y Z f g empty) := g
-- | A B D (@prod_mk_coprod _ _ W X Y Z f g) := g

-- @[simp] lemma comp_snd_prod_mk {X Y Z : prod_coprod C} (f : norm_hom X Y) (g : norm_hom X Z) :
--   comp_snd (prod_mk f g) = g :=
-- by cases X; simp [comp_snd, prod_mk]

-- lemma prod_eta : Π {X Y Z : prod_coprod C} (f : norm_hom X (prod Y Z)),
--   prod_mk (comp_fst f) (comp_snd f) = f
-- | _ _ _ (prod_mk_of_cat f g empty) := rfl
-- | _ _ _ (prod_mk_prod f g empty) := rfl
-- | _ _ _ (prod_mk_coprod f g) := rfl

-- def coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
--   norm_hom (coprod X Y) Z
-- | _ _ (of_cat' _) f g := coprod_mk_of_cat empty f g
-- | _ _ (coprod _ _) f g := coprod_mk_coprod empty f g
-- | _ _ (prod _ _) f g := prod_mk_coprod
--   (coprod_mk (comp_fst f) (comp_fst g))
--   (coprod_mk (comp_snd f) (comp_snd g))

-- lemma coprod_mk_comp_fst : Π {W X Y Z : prod_coprod C}
--   (f : norm_hom W (prod Y Z)) (g : norm_hom X (prod Y Z)),
--   comp_fst (coprod_mk f g) = coprod_mk (comp_fst f) (comp_fst g) :=
-- begin
--   intros,
--   cases Y;
--   dsimp [coprod_mk, comp_fst]; refl
-- end

-- lemma coprod_mk_comp_snd : Π {W X Y Z : prod_coprod C}
--   (f : norm_hom W (prod Y Z)) (g : norm_hom X (prod Y Z)),
--   comp_snd (coprod_mk f g) = coprod_mk (comp_snd f) (comp_snd g) :=
-- begin
--   intros,
--   cases Y;
--   dsimp [coprod_mk, comp_fst]; refl
-- end

-- def inl_comp : Π {X Y Z : prod_coprod C}, norm_hom (coprod X Y) Z → norm_hom X Z
-- | _ _ _ (coprod_mk_of_cat empty g h) := g
-- | _ _ _ (coprod_mk_coprod empty g h) := g
-- | _ _ _ (@prod_mk_coprod _ _ W X Y Z f g) := prod_mk (inl_comp f) (inl_comp g)

-- def inr_comp : Π {X Y Z : prod_coprod C}, norm_hom (coprod X Y) Z → norm_hom Y Z
-- | _ _ _ (coprod_mk_of_cat empty g h) := h
-- | _ _ _ (coprod_mk_coprod empty g h) := h
-- | _ _ _ (@prod_mk_coprod _ _ W X Y Z f g) := prod_mk (inr_comp f) (inr_comp g)

-- lemma inl_comp_comp_fst : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
--   inl_comp (comp_fst f) = comp_fst (inl_comp f)
-- | A B D _ (prod_mk_coprod f g) := by simp [comp_fst, inl_comp]

-- lemma inr_comp_comp_fst : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
--   inr_comp (comp_fst f) = comp_fst (inr_comp f)
-- | A B D _ (prod_mk_coprod f g) := by simp [comp_fst, inr_comp]

-- lemma inl_comp_comp_snd : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
--   inl_comp (comp_snd f) = comp_snd (inl_comp f)
-- | A B D _ (prod_mk_coprod f g) := by simp [comp_snd, inl_comp]

-- lemma inr_comp_comp_snd : Π {W X Y Z : prod_coprod C} (f : norm_hom (coprod W X) (prod Y Z)),
--   inr_comp (comp_snd f) = comp_snd (inr_comp f)
-- | A B D _ (prod_mk_coprod f g) := by simp [comp_snd, inr_comp]

-- @[simp] lemma inl_comp_coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
--   inl_comp (coprod_mk f g) = f
-- | _ _ (of_cat' Z) _ _ := rfl
-- | _ _ (coprod Y Z) _ _ := rfl
-- | _ _ (prod Y Z) f g :=
-- by rw [coprod_mk, inl_comp, inl_comp_coprod_mk, inl_comp_coprod_mk, prod_eta]

-- @[simp] lemma inr_comp_coprod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom X Z) (g : norm_hom Y Z),
--   inr_comp (coprod_mk f g) = g
-- | _ _ (of_cat' Z) _ _ := rfl
-- | _ _ (coprod Y Z) _ _ := rfl
-- | _ _ (prod Y Z) f g :=
-- by rw [coprod_mk, inr_comp, inr_comp_coprod_mk, inr_comp_coprod_mk, prod_eta]

-- lemma coprod_eta : Π {X Y Z : prod_coprod C} (f : norm_hom (coprod X Y) Z),
--   coprod_mk (inl_comp f) (inr_comp f) = f
-- | _ _ _ (coprod_mk_of_cat empty g h) := rfl
-- | _ _ _ (coprod_mk_coprod empty g h) := rfl
-- | _ _ _ (prod_mk_coprod f g) :=
--   by simp [coprod_mk, inl_comp, inr_comp, coprod_eta f, coprod_eta g]

-- def prod_mk_l : Π {W X Y Z : prod_coprod C} (f : norm_hom W X) (g : norm_hom W Y)
--   (h : list_inj (prod X Y) Z), norm_hom W Z
-- | (of_cat' _) _ _ _ f g h := prod_mk_of_cat f g h
-- | (coprod V W) X Y Z f g h :=
--   coprod_mk
--     (prod_mk_l (inl_comp f) (inl_comp g) h)
--     (prod_mk_l (inr_comp f) (inr_comp g) h)
-- | (prod _ _) _ _ _ f g h := prod_mk_prod f g h

-- def coprod_mk_l : Π {W X Y Z : prod_coprod C} (f : list_proj W (coprod X Y))
--   (g : norm_hom X Z) (h : norm_hom Y Z), norm_hom W Z
-- | _ _ _ (of_cat' _) f g h := coprod_mk_of_cat f g h
-- | X Y Z (prod V W) f g h :=
--   prod_mk
--     (coprod_mk_l f (comp_fst g) (comp_fst h))
--     (coprod_mk_l f (comp_snd g) (comp_snd h))
-- | _ _ _ (coprod _ _) f g h := coprod_mk_coprod f g h

-- def fst_comp : Π {X Y Z : prod_coprod C}
--   (f : norm_hom X Z), norm_hom (prod X Y) Z
-- | _ _ _ (prod_mk_of_cat f g h) :=
--   prod_mk_l (fst_comp f) (fst_comp g) h
-- | _ _ _ (prod_mk_prod f g h) :=
--   prod_mk_l (fst_comp f) (fst_comp g) h
-- | _ _ _ (prod_mk_coprod f g) :=
--   prod_mk (fst_comp f) (fst_comp g)
-- | _ _ _ (coprod_mk_of_cat f g h) := coprod_mk_of_cat f.fst_comp g h
-- | _ _ _ (coprod_mk_coprod f g h) := coprod_mk_coprod f.fst_comp g h
-- | _ _ _ (of_cat f g h) := of_cat f.fst_comp g h

-- def snd_comp : Π {X Y Z : prod_coprod C}
--   (f : norm_hom Y Z), norm_hom (prod X Y) Z
-- | _ _ _ (prod_mk_of_cat f g h) :=
--   prod_mk_l (snd_comp f) (snd_comp g) h
-- | _ _ _ (prod_mk_prod f g h) :=
--   prod_mk_l (snd_comp f) (snd_comp g) h
-- | _ _ _ (prod_mk_coprod f g) :=
--   prod_mk (snd_comp f) (snd_comp g)
-- | _ _ _ (coprod_mk_of_cat f g h) := coprod_mk_of_cat f.snd_comp g h
-- | _ _ _ (coprod_mk_coprod f g h) := coprod_mk_coprod f.snd_comp g h
-- | _ _ _ (of_cat f g h) := of_cat f.snd_comp g h

def comp {X Y Z : prod_coprod C} {b₁ b₂ : bool} (f : norm_hom b₁  X Y) (g : norm_hom b₂ Y Z) :
  Σ b : bool, norm_hom b X Z :=
norm_hom2.to_norm_hom (norm_hom2.comp (to_norm_hom2 f) g.to_norm_hom2)

@[simp] def norm_syntax : Π {X Y : prod_coprod C} (f : syntax X Y),
  Σ b : bool, norm_hom b X Y
| _ _ (syntax.of_cat f) := ⟨ff, norm_hom.of_cat f⟩
| _ _ (syntax.id _) := ⟨_, norm_hom.id _⟩
| _ _ (syntax.comp f g) := (norm_syntax f).2.comp (norm_syntax g).2
| _ _ syntax.fst := norm_hom.fst_comp (norm_hom.id _)
| _ _ syntax.snd := norm_hom.snd_comp (norm_hom.id _)
| _ _ (syntax.prod_mk f g) := ⟨ff, norm_hom.prod_mk (norm_syntax f).2 (norm_syntax g).2⟩
| _ _ syntax.inl := norm_hom.comp_inl (norm_hom.id _)
| _ _ syntax.inr := norm_hom.comp_inr (norm_hom.id _)
| _ _ (syntax.coprod_mk f g) := ⟨ff, norm_hom.coprod_mk (norm_syntax f).2 (norm_syntax g).2⟩
#exit
@[simp] lemma to_hom_comp_inl : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Y))),
  (@norm_hom.comp_inl _ _ _ _ Z f).to_norm_hom2.to_hom = f.to_norm_hom2.to_hom ≫ inl
| (of_cat' X) _ _ f := by simp [norm_hom.comp_inl]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) :=
  by ext; simp [norm_hom.comp_inl, to_hom_comp_inl f, to_hom_comp_inl g,
    ← category.assoc]
| (prod W X) Y Z (norm_hom.fst_comp f) := by simp [norm_hom.comp_inl, to_hom_comp_inl f]
| (prod W X) Y Z (norm_hom.snd_comp f) := by simp [norm_hom.comp_inl, to_hom_comp_inl f]
| (prod W X) Y Z (norm_hom.of_not_proj f) :=
  by simp [norm_hom.comp_inl, to_hom_comp_inl f.of_not_proj]

@[simp] lemma to_hom_comp_inr : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Z))),
  (@norm_hom.comp_inr _ _ X Y Z f).to_norm_hom2.to_hom = f.to_norm_hom2.to_hom ≫ inr
| (of_cat' X) _ _ f := by simp [norm_hom.comp_inr]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) :=
  by ext; simp [norm_hom.comp_inr, to_hom_comp_inr f, to_hom_comp_inr g,
    ← category.assoc]
| (prod W X) Y Z (norm_hom.fst_comp f) := by simp [norm_hom.comp_inr, to_hom_comp_inr f]
| (prod W X) Y Z (norm_hom.snd_comp f) := by simp [norm_hom.comp_inr, to_hom_comp_inr f]
| (prod W X) Y Z (norm_hom.of_not_proj f) :=
  by simp [norm_hom.comp_inr, to_hom_comp_inr f.of_not_proj]

@[simp] lemma to_hom_prod_mk : Π {X Y Z : prod_coprod C} (f : norm_hom (sum.inl (X, Y)))
  (g : norm_hom (sum.inl (X, Z))),
  (f.prod_mk g).to_norm_hom2.to_hom = prod_mk f.to_norm_hom2.to_hom g.to_norm_hom2.to_hom
| (of_cat' X) Y Z f g := by simp [norm_hom.prod_mk]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.fst_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.snd_comp g) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g]
| (prod W X) Y Z (norm_hom.fst_comp f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g.of_not_proj]
| (prod W X) Y Z (norm_hom.snd_comp f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g.of_not_proj]
| (prod W X) Y Z (norm_hom.of_not_proj f) (norm_hom.of_not_proj g)  :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f.of_not_proj, to_hom_prod_mk g.of_not_proj]
| (coprod W X) Y Z (norm_hom.coprod_mk f g) (norm_hom.coprod_mk h i) :=
  by ext; simp [norm_hom.prod_mk, to_hom_prod_mk f, to_hom_prod_mk g]

@[simp] lemma to_hom_comp : Π {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 Y Z),
  (f.comp g).to_hom = f.to_hom ≫ g.to_hom
| _ _ _ (norm_hom2.coprod_mk f g) h :=
  by ext; simp [to_hom_comp f, to_hom_comp g, ← category.assoc]
| _ _ _ (norm_hom2.fst_comp f) g :=
  by simp [to_hom_comp f]
| _ _ _ (norm_hom2.snd_comp f) g :=
  by simp [to_hom_comp f]
-- | _ _ _ f (norm_hom2.prod_mk g h) :=
-- | _ _ _ f (norm_hom2.comp_inl g) := g)
-- | _ _ _ f (norm_hom2.comp_inr g) :=
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.of_cat g) :=
  by simp
| _ _ _ (norm_hom2.comp_inl f) (norm_hom2.coprod_mk g h) :=
  by simp [to_hom_comp f]
| _ _ _ (norm_hom2.comp_inr f) (norm_hom2.coprod_mk g h) :=
  by simp [to_hom_comp f]
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.fst_comp h) :=
  by simp [to_hom_comp _ h, ← category.assoc]
| _ _ _  (norm_hom2.prod_mk f g) (norm_hom2.snd_comp h) :=
  by simp [to_hom_comp _ h, ← category.assoc]
--repeated cases
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.of_cat f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ (norm_hom2.comp_inl f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ (norm_hom2.comp_inr f) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f'@(norm_hom2.comp_inl f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ f'@(norm_hom2.comp_inr f) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inl g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.comp_inr g) :=
  by simp [to_hom_comp _ g]
| _ _ _ f@(norm_hom2.prod_mk _ _) (norm_hom2.prod_mk g h) :=
  by ext; simp [to_hom_comp _ g, to_hom_comp _ h]



#exit
