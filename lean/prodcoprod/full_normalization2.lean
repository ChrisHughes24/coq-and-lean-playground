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

inductive norm_hom : Π (b : bool), prod_coprod C → prod_coprod C → Type
| of_cat {X Y : C} : (X ⟶ Y) → norm_hom ff (of_cat' X) (of_cat' Y)
| coprod_mk {X Y Z : prod_coprod C} {b₁ b₂ : bool} :
  norm_hom b₁ X Z → norm_hom b₂ Y Z → norm_hom ff (coprod X Y) Z
| prod_mk_of_cat {X : C} {Y Z : prod_coprod C} : norm_hom ff (of_cat' X) Y →
  norm_hom ff (of_cat' X) Z → norm_hom ff (of_cat' X) (prod Y Z)
| prod_mk_prod {W X Y Z : prod_coprod C} {b₁ b₂ : bool}
  (f : norm_hom b₁ (prod W X) Y) (g : norm_hom b₂ (prod W X) Z) : norm_hom ff (prod W X) (prod Y Z)
| fst_comp_of_cat {X Y : prod_coprod C} {Z : C} {b : bool} (f : norm_hom b X (of_cat' Z)) :
  norm_hom tt (prod X Y) (of_cat' Z)
| snd_comp_of_cat {X Y : prod_coprod C} {Z : C} {b : bool} (f : norm_hom b Y (of_cat' Z)) :
  norm_hom tt (prod X Y) (of_cat' Z)
| comp_inl_of_cat {X : C} {Y Z : prod_coprod C} (f : norm_hom ff (of_cat' X) Y) :
  norm_hom ff (of_cat' X) (coprod Y Z)
| comp_inr_of_cat {X : C} {Y Z : prod_coprod C} (f : norm_hom ff (of_cat' X) Z) :
  norm_hom ff (of_cat' X) (coprod Y Z)
| fst_comp_coprod {W X Y Z : prod_coprod C} {b : bool} (f : norm_hom b W (coprod Y Z)) :
  norm_hom tt (prod W X) (coprod Y Z)
| snd_comp_coprod {W X Y Z : prod_coprod C} {b : bool} (f : norm_hom b X (coprod Y Z)) :
  norm_hom tt (prod W X) (coprod Y Z)
| comp_inl_prod {W X Y Z : prod_coprod C} (f : norm_hom ff (prod W X) Y) :
  norm_hom ff (prod W X) (coprod Y Z)
| comp_inr_prod {W X Y Z : prod_coprod C} (f : norm_hom ff (prod W X) Z) :
  norm_hom ff (prod W X) (coprod Y Z)

variables {W X Y Z : prod_coprod C}

namespace norm_hom

def prod_mk : Π {X Y Z : prod_coprod C} {b₁ b₂ : bool} (f : norm_hom b₁ X Y) (g : norm_hom b₂ X Z),
  norm_hom ff X (prod Y Z)
| (of_cat' X) _ _ ff ff f g := prod_mk_of_cat f g
| (prod X Y) _ _ _ _ f g := prod_mk_prod f g
| (coprod X Y) _ _ _ _ (coprod_mk f g) (coprod_mk h i) :=
  coprod_mk (prod_mk f h) (prod_mk g i)

def comp_fst : Π {X Y Z : prod_coprod C} {b : bool} (f : norm_hom b X (prod Y Z)),
  Σ b, norm_hom b X Y
| _ _ _ _ (prod_mk_of_cat f g) := ⟨_, f⟩
| _ _ _ _ (prod_mk_prod f g) := ⟨_, f⟩
| _ _ _ _ (coprod_mk f g) := ⟨_, coprod_mk (comp_fst f).2 (comp_fst g).2⟩

def comp_snd : Π {X Y Z : prod_coprod C} {b : bool} (f : norm_hom b X (prod Y Z)),
  Σ b, norm_hom b X Z
| _ _ _ _ (prod_mk_of_cat f g) := ⟨_, g⟩
| _ _ _ _ (prod_mk_prod f g) := ⟨_, g⟩
| _ _ _ _ (coprod_mk f g) := ⟨_, coprod_mk (comp_snd f).2 (comp_snd g).2⟩

def fst_comp : Π {X Y Z : prod_coprod C} {b : bool}, norm_hom b X Z →
  Σ b' : bool, norm_hom b' (prod X Y) Z
| _ _ (of_cat' X) _ f := ⟨tt, fst_comp_of_cat f⟩
| _ _ (coprod X Y) _ f := ⟨tt, fst_comp_coprod f⟩
| _ _ (prod X Y) _ (prod_mk_of_cat f g) := ⟨ff, prod_mk_prod (fst_comp f).2 (fst_comp g).2⟩
| _ _ (prod X Y) _ (prod_mk_prod f g) := ⟨ff, prod_mk_prod (fst_comp f).2 (fst_comp g).2⟩
| _ _ (prod X Y) ff (coprod_mk f g) :=
  ⟨ff, prod_mk (fst_comp (coprod_mk (comp_fst f).2 (comp_fst g).2)).2
    (fst_comp (coprod_mk (comp_snd f).2 (comp_snd g).2)).2⟩

def snd_comp : Π {X Y Z : prod_coprod C} {b : bool}, norm_hom b Y Z →
  Σ b' : bool, norm_hom b' (prod X Y) Z
| _ _ (of_cat' X) _ f := ⟨tt, snd_comp_of_cat f⟩
| _ _ (coprod X Y) _ f := ⟨tt, snd_comp_coprod f⟩
| _ _ (prod X Y) _ (prod_mk_of_cat f g) := ⟨ff, prod_mk_prod (snd_comp f).2 (snd_comp g).2⟩
| _ _ (prod X Y) _ (prod_mk_prod f g) := ⟨ff, prod_mk_prod (snd_comp f).2 (snd_comp g).2⟩
| _ _ (prod X Y) ff (coprod_mk f g) :=
  ⟨ff, prod_mk (snd_comp (coprod_mk (comp_fst f).2 (comp_fst g).2)).2
    (snd_comp (coprod_mk (comp_snd f).2 (comp_snd g).2)).2⟩

def comp_inl : Π {X Y Z : prod_coprod C} {b : bool}, norm_hom b X Y → Σ b, norm_hom b X (coprod Y Z)
| (of_cat' X) _ _ ff f := ⟨_, comp_inl_of_cat f⟩
| (coprod W X) Y Z b (coprod_mk f g) := ⟨_, coprod_mk (comp_inl f).2 (comp_inl g).2⟩
| (prod X Y) _ _ ff f := ⟨_, comp_inl_prod f⟩
| (prod X Y) _ _ tt (fst_comp_of_cat f) := ⟨_, (fst_comp (comp_inl f).2).2⟩
| (prod X Y) _ _ tt (fst_comp_coprod f) := ⟨_, (fst_comp (comp_inl f).2).2⟩
| (prod X Y) _ _ tt (snd_comp_of_cat f) := ⟨_, (snd_comp (comp_inl f).2).2⟩
| (prod X Y) _ _ tt (snd_comp_coprod f) := ⟨_, (snd_comp (comp_inl f).2).2⟩

def comp_inr : Π {X Y Z : prod_coprod C} {b : bool}, norm_hom b X Z → Σ b, norm_hom b X (coprod Y Z)
| (of_cat' X) _ _ ff f := ⟨_, comp_inr_of_cat f⟩
| (coprod W X) Y Z b (coprod_mk f g) := ⟨_, coprod_mk (comp_inr f).2 (comp_inr g).2⟩
| (prod X Y) _ _ ff f := ⟨_, comp_inr_prod f⟩
| (prod X Y) _ _ tt (fst_comp_of_cat f) := ⟨_, (fst_comp (comp_inr f).2).2⟩
| (prod X Y) _ _ tt (fst_comp_coprod f) := ⟨_, (fst_comp (comp_inr f).2).2⟩
| (prod X Y) _ _ tt (snd_comp_of_cat f) := ⟨_, (snd_comp (comp_inr f).2).2⟩
| (prod X Y) _ _ tt (snd_comp_coprod f) := ⟨_, (snd_comp (comp_inr f).2).2⟩

def norm_hom.id : Π (X : prod_coprod C), norm_hom ff X X
| (of_cat' X) := norm_hom.of_cat (𝟙 X)
| (prod X Y) := norm_hom.prod_mk (norm_hom.fst_comp (norm_hom.id X)).2 (norm_hom.snd_comp (norm_hom.id Y)).2
| (coprod X Y) := norm_hom.coprod_mk (norm_hom.comp_inl (norm_hom.id X)).2 (norm_hom.comp_inr (norm_hom.id Y)).2

lemma comp_inl_coprod_mk : Π {W X Y Z : prod_coprod C} {b₁ b₂ : bool}
  (f : norm_hom b₁ X Z) (g : norm_hom b₂ Y Z), @comp_inl _ _ _ _ W _ (coprod_mk f g) =
    ⟨ff, coprod_mk (comp_inl f).2 (comp_inl g).2⟩ :=
by intros; simp [comp_inl]

lemma comp_inr_coprod_mk : Π {W X Y Z : prod_coprod C} {b₁ b₂ : bool}
  (f : norm_hom b₁ X Z) (g : norm_hom b₂ Y Z), @comp_inr _ _ _ W _ _ (coprod_mk f g) =
    ⟨ff, coprod_mk (comp_inr f).2 (comp_inr g).2⟩ :=
by intros; simp [comp_inr]

@[simp] lemma prod_mk_comp_fst : Π {X Y Z : prod_coprod C} {b₁ b₂ : bool}
  (f : norm_hom b₁ X Y) (g : norm_hom b₂ X Z),
  @comp_fst _ _ _ Y _ _ (prod_mk f g) = ⟨_, f⟩
| (of_cat' X) _ _ ff ff f g := by simp [prod_mk, comp_fst]
| (prod X Y) _ _ _ _ f g := by simp [prod_mk, comp_fst]
| (coprod X Y) _ _ _ _ (coprod_mk f g) (coprod_mk h i) :=
  by rw [prod_mk, comp_fst, prod_mk_comp_fst f h, prod_mk_comp_fst g i]

@[simp] lemma prod_mk_comp_snd : Π {X Y Z : prod_coprod C} {b₁ b₂ : bool}
  (f : norm_hom b₁ X Y) (g : norm_hom b₂ X Z),
  @comp_snd _ _ X _ _ _ (prod_mk f g) = ⟨_, g⟩
| (of_cat' X) _ _ ff ff f g := by simp [prod_mk, comp_snd]
| (prod X Y) _ _ _ _ f g := by simp [prod_mk, comp_snd]
| (coprod X Y) _ _ _ _ (coprod_mk f g) (coprod_mk h i) :=
  by rw [prod_mk, comp_snd, prod_mk_comp_snd f h, prod_mk_comp_snd g i]

lemma fst_comp_prod_mk : Π {W X Y Z : prod_coprod C} {b₁ b₂ : bool}
  (f : norm_hom b₁ X Y) (g : norm_hom b₂ X Z),
  @fst_comp _ _ _ W _ _ (prod_mk f g) =
  ⟨ff, prod_mk (fst_comp f).2 (fst_comp g).2⟩
| _ (of_cat' X) _ _ ff ff f g := by simp [prod_mk, fst_comp]
| _ (prod X Y) _ _ _ _ f g := by simp [prod_mk, fst_comp]
| _ (coprod X Y) _ _ _ _ (coprod_mk f g) (coprod_mk h i) :=
  begin
    simp [prod_mk, fst_comp],
    rw [prod_mk_comp_fst, prod_mk_comp_fst,
      prod_mk_comp_snd, prod_mk_comp_snd],
    simp [fst_comp_prod_mk f h, fst_comp_prod_mk g i]
  end

lemma snd_comp_prod_mk : Π {W X Y Z : prod_coprod C} {b₁ b₂ : bool}
  (f : norm_hom b₁ X Y) (g : norm_hom b₂ X Z),
  @snd_comp _ _ W _ _ _ (prod_mk f g) =
  ⟨ff, prod_mk (snd_comp f).2 (snd_comp g).2⟩
| _ (of_cat' X) _ _ ff ff f g := by simp [prod_mk, snd_comp]
| _ (prod X Y) _ _ _ _ f g := by simp [prod_mk, snd_comp]
| _ (coprod X Y) _ _ _ _ (coprod_mk f g) (coprod_mk h i) :=
  begin
    simp [prod_mk, snd_comp],
    rw [prod_mk_comp_fst, prod_mk_comp_fst,
      prod_mk_comp_snd, prod_mk_comp_snd],
    simp [snd_comp_prod_mk f h, snd_comp_prod_mk g i]
  end

example {W X Y Z : C}

lemma fst_comp_comp_inl : Π {W X Y Z : prod_coprod C} {b₁ : bool}
  (f : norm_hom b₁ X Y),
  (f.fst_comp.2.comp_inl : Σ b : bool, norm_hom _ (prod X W) (coprod Y Z)) =
  f.comp_inl.2.fst_comp :=
begin
  intros,
  induction f,
  { dsimp [comp_inl, fst_comp]; try { simp * } },
  { admit },
  { dsimp [comp_inl, fst_comp]; try { simp * }, admit },
  { rw [comp_inl, fst_comp],
     },

end


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

set_option eqn_compiler.lemmas false

def to_norm_hom2 : Π {X Y : prod_coprod C} {b : bool} (f : norm_hom b X Y),
  norm_hom2 X Y
| _ _ _ (of_cat f) := norm_hom2.of_cat f
| _ _ _ (coprod_mk f g) := norm_hom2.coprod_mk (to_norm_hom2 f) (to_norm_hom2 g)
| _ _ _ (prod_mk_of_cat f g) := norm_hom2.prod_mk (to_norm_hom2 f) (to_norm_hom2 g)
| _ _ _ (prod_mk_prod f g) := norm_hom2.prod_mk (to_norm_hom2 f) (to_norm_hom2 g)
| _ _ _ (fst_comp_of_cat f) := norm_hom2.fst_comp (to_norm_hom2 f)
| _ _ _ (snd_comp_of_cat f) := norm_hom2.snd_comp (to_norm_hom2 f)
| _ _ _ (fst_comp_coprod f) := norm_hom2.fst_comp (to_norm_hom2 f)
| _ _ _ (snd_comp_coprod f) := norm_hom2.snd_comp (to_norm_hom2 f)
| _ _ _ (comp_inl_of_cat f) := norm_hom2.comp_inl (to_norm_hom2 f)
| _ _ _ (comp_inr_of_cat f) := norm_hom2.comp_inr (to_norm_hom2 f)
| _ _ _ (comp_inl_prod f) := norm_hom2.comp_inl (to_norm_hom2 f)
| _ _ _ (comp_inr_prod f) := norm_hom2.comp_inr (to_norm_hom2 f)

inductive norm_hom2.rel : Π {X Y : prod_coprod C} (f g : norm_hom2 X Y), Prop
| refl {X Y : prod_coprod C} (f : norm_hom2 X Y) : norm_hom2.rel f f
| symm {X Y : prod_coprod C} {f g : norm_hom2 X Y} : norm_hom2.rel f g → norm_hom2.rel g f
| trans {X Y : prod_coprod C} {f g h : norm_hom2 X Y} : norm_hom2.rel f g → norm_hom2.rel g h → norm_hom2.rel f h
| prod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom2 X Y} {g₁ g₂ : norm_hom2 X Z} :
  norm_hom2.rel f₁ f₂ → norm_hom2.rel g₁ g₂ → norm_hom2.rel (f₁.prod_mk g₁) (f₂.prod_mk g₂)
| coprod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom2 X Z} {g₁ g₂ : norm_hom2 Y Z} :
  norm_hom2.rel f₁ f₂ → norm_hom2.rel g₁ g₂ → norm_hom2.rel (f₁.coprod_mk g₁) (f₂.coprod_mk g₂)
| comp_inl_congr {X Y Z : prod_coprod C} (f₁ f₂ : norm_hom2 X Y) :
  norm_hom2.rel f₁ f₂ → norm_hom2.rel (f₁.comp_inl : norm_hom2 X (coprod Y Z)) f₂.comp_inl
| comp_inr_congr {X Y Z : prod_coprod C} (f₁ f₂ : norm_hom2 X Y) :
  norm_hom2.rel f₁ f₂ → norm_hom2.rel (f₁.comp_inr : norm_hom2 X (coprod Z Y)) f₂.comp_inr
| fst_comp_congr {X Y Z : prod_coprod C} (f₁ f₂ : norm_hom2 X Y) :
  norm_hom2.rel f₁ f₂ → norm_hom2.rel (f₁.fst_comp : norm_hom2 (prod X Z) Y) f₂.fst_comp
| snd_comp_congr {X Y Z : prod_coprod C} (f₁ f₂ : norm_hom2 X Y) :
  norm_hom2.rel f₁ f₂ → norm_hom2.rel (f₁.snd_comp : norm_hom2 (prod Z X) Y) f₂.snd_comp
| comp_inl_coprod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Z) (g : norm_hom2 Y Z) :
  norm_hom2.rel (@norm_hom2.comp_inl _ _ _ _ Z (norm_hom2.coprod_mk f g))
    (norm_hom2.coprod_mk f.comp_inl g.comp_inl)
| comp_inr_coprod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Z) (g : norm_hom2 Y Z) :
  norm_hom2.rel (@norm_hom2.comp_inr _ _ _ Y _ (norm_hom2.coprod_mk f g))
    (norm_hom2.coprod_mk f.comp_inr g.comp_inr)
| fst_comp_prod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 X Z) :
  norm_hom2.rel (@norm_hom2.fst_comp _ _ _ Y _ (norm_hom2.prod_mk f g))
    (norm_hom2.prod_mk f.fst_comp g.fst_comp)
| snd_comp_prod_mk {X Y Z : prod_coprod C} (f : norm_hom2 X Y) (g : norm_hom2 X Z) :
  norm_hom2.rel (@norm_hom2.snd_comp _ _ Y _ _ (norm_hom2.prod_mk f g))
    (norm_hom2.prod_mk f.snd_comp g.snd_comp)
| fst_comp_comp_inl {W X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
  norm_hom2.rel (f.fst_comp.comp_inl : norm_hom2 (prod X W) (coprod Y Z)) f.comp_inl.fst_comp
| snd_comp_comp_inl {W X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
  norm_hom2.rel (f.snd_comp.comp_inl : norm_hom2 (prod W X) (coprod Y Z)) f.comp_inl.snd_comp
| fst_comp_comp_inr {W X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
  norm_hom2.rel (f.fst_comp.comp_inr : norm_hom2 (prod X W) (coprod Z Y)) f.comp_inr.fst_comp
| snd_comp_comp_inr {W X Y Z : prod_coprod C} (f : norm_hom2 X Y) :
  norm_hom2.rel (f.snd_comp.comp_inr : norm_hom2 (prod W X) (coprod Z Y)) f.comp_inr.snd_comp

set_option eqn_compiler.lemmas true

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

@[simp] def norm_hom2.to_norm_hom : Π {X Y : prod_coprod C} (f :norm_hom2 X Y),
  Σ b : bool, norm_hom b X Y
| _ _ (norm_hom2.of_cat f) := ⟨_, norm_hom.of_cat f⟩
| _ _ (norm_hom2.comp_inl f) := norm_hom.comp_inl (norm_hom2.to_norm_hom f).2
| _ _ (norm_hom2.comp_inr f) := norm_hom.comp_inr (norm_hom2.to_norm_hom f).2
| _ _ (norm_hom2.fst_comp f) := norm_hom.fst_comp (norm_hom2.to_norm_hom f).2
| _ _ (norm_hom2.snd_comp f) := norm_hom.snd_comp (norm_hom2.to_norm_hom f).2
| _ _ (norm_hom2.prod_mk f g) := ⟨ff, norm_hom.prod_mk (norm_hom2.to_norm_hom f).2 (norm_hom2.to_norm_hom g).2⟩
| _ _ (norm_hom2.coprod_mk f g) := ⟨ff, norm_hom.coprod_mk (norm_hom2.to_norm_hom f).2 (norm_hom2.to_norm_hom g).2⟩

lemma to_norm_hom_rel : Π {X Y : prod_coprod C} (f g : norm_hom2 X Y) (h : norm_hom2.rel f g),
  f.to_norm_hom = g.to_norm_hom :=
begin
  intros X Y f g h,
  induction h;
  try { dsimp only [norm_hom2.to_norm_hom] },
  { refl },
  { symmetry, assumption },
  { transitivity, assumption, assumption },
  { rw [h_ih_ᾰ, h_ih_ᾰ_1] },
  { rw [h_ih_ᾰ, h_ih_ᾰ_1] },
  { rw [h_ih] },
  { rw [h_ih] },
  { rw [h_ih] },
  { rw [h_ih] },
  { refl },
  { refl },
  { rw [norm_hom.fst_comp_prod_mk] },
  { rw [norm_hom.snd_comp_prod_mk] },
  { dsimp [comp_inl] }

end

@[simp] def norm_hom2.to_hom : Π {X Y : prod_coprod C} (f : norm_hom2 X Y), (X ⟶ Y)
| _ _ (norm_hom2.of_cat f) := prod_coprod.of_cat.map f
| _ _ (norm_hom2.comp_inl f) := norm_hom2.to_hom f ≫ inl
| _ _ (norm_hom2.comp_inr f) := norm_hom2.to_hom f ≫ inr
| _ _ (norm_hom2.fst_comp f) := fst ≫ norm_hom2.to_hom f
| _ _ (norm_hom2.snd_comp f) := snd ≫ norm_hom2.to_hom f
| _ _ (norm_hom2.prod_mk f g) := prod_coprod.prod_mk (norm_hom2.to_hom f) (norm_hom2.to_hom g)
| _ _ (norm_hom2.coprod_mk f g) := prod_coprod.coprod_mk (norm_hom2.to_hom f) (norm_hom2.to_hom g)

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
