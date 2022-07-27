import category_theory.limits.presheaf

open category_theory

noncomputable theory

variables (C : Type) [category.{0} C]

inductive prod_coprod : Type
| of_cat' : C → prod_coprod
| prod : prod_coprod → prod_coprod → prod_coprod
| coprod : prod_coprod → prod_coprod → prod_coprod

variable {C}

namespace prod_coprod


inductive norm_hom : bool → Π (X Y : prod_coprod C), Type
| of_cat_ff {X Y : C} : (X ⟶ Y) → norm_hom ff (of_cat' X) (of_cat' Y)
| prod_mk_ff {X Y Z : prod_coprod C} : norm_hom tt X Y → norm_hom tt X Z → norm_hom ff X (Y.prod Z)
| fst_ff {X Y : prod_coprod C} : norm_hom ff (X.prod Y) X
| snd_ff {X Y : prod_coprod C} : norm_hom ff (X.prod Y) Y
| coprod_mk_ff {X Y Z : prod_coprod C} : norm_hom tt X Z → norm_hom tt Y Z → norm_hom ff (X.coprod Y) Z
| inl_ff {X Y : prod_coprod C} : norm_hom ff X (X.coprod Y)
| inr_ff {X Y : prod_coprod C} : norm_hom ff Y (X.coprod Y)
| id (X : prod_coprod C) : norm_hom tt X X
| comp_ff {X Y Z : prod_coprod C} : norm_hom ff X Y → norm_hom tt Y Z → norm_hom tt X Z

namespace norm_hom

@[simp] def of_ff {X Y : prod_coprod C} (f : norm_hom ff X Y) : norm_hom tt X Y :=
norm_hom.comp_ff f (norm_hom.id _)

def of_cat {X Y : C} (f : X ⟶ Y) : norm_hom tt (of_cat' X) (of_cat' Y) :=
of_ff (norm_hom.of_cat_ff f)

def prod_mk {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt X Z) : norm_hom tt X (Y.prod Z) :=
of_ff (norm_hom.prod_mk_ff f g)

def fst {X Y : prod_coprod C} : norm_hom tt (X.prod Y) X :=
of_ff norm_hom.fst_ff

def snd {X Y : prod_coprod C} : norm_hom tt (X.prod Y) Y :=
of_ff norm_hom.snd_ff

def coprod_mk {X Y Z : prod_coprod C} (f : norm_hom tt X Z) (g : norm_hom tt Y Z) : norm_hom tt (X.coprod Y) Z :=
of_ff (norm_hom.coprod_mk_ff f g)

def inl {X Y : prod_coprod C} : norm_hom tt X (X.coprod Y) :=
of_ff norm_hom.inl_ff

def inr {X Y : prod_coprod C} : norm_hom tt Y (X.coprod Y) :=
of_ff norm_hom.inr_ff

@[elab_as_eliminator] def norm_hom.rec_on_tt {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X Y : prod_coprod C} (f : norm_hom tt X Y)
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom ff X Y) (g : norm_hom tt Y Z), motive Y Z g →
    motive X Z (f.comp_ff g)) :
  motive X Y f :=
have ∀ (b : bool) (f : norm_hom b X Y) (h : b = tt), motive X Y (eq.rec_on h f),
  from λ b f, begin
    induction f; try {dsimp; intros; contradiction},
    { intros, apply h₁ },
    { intros h, apply h₂,
      tauto }
  end,
this tt f rfl

@[simp] lemma norm_hom.rec_on_tt_id  {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X : prod_coprod C}
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom ff X Y) (g : norm_hom tt Y Z), motive Y Z g →
    motive X Z (f.comp_ff g)) :
  @norm_hom.rec_on_tt C _ motive X X (norm_hom.id X) h₁ h₂ = h₁ X := rfl

@[simp] lemma norm_hom.rec_on_tt_comp_ff {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X Y Z : prod_coprod C} (f : norm_hom ff X Y) (g : norm_hom tt Y Z)
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom ff X Y) (g : norm_hom tt Y Z), motive Y Z g →
    motive X Z (f.comp_ff g)) :
  @norm_hom.rec_on_tt C _ motive X Z (norm_hom.comp_ff f g) h₁ h₂ = h₂ X Y Z f g
    (@norm_hom.rec_on_tt C _ motive Y Z g h₁ h₂) := rfl

def comp {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt Y Z) : norm_hom tt X Z :=
norm_hom.rec_on_tt f (λ _ g, g) (λ _ _ _ f _ ih g, norm_hom.comp_ff f (ih g)) g

lemma comp_id {X Y : prod_coprod C} (f : norm_hom tt X Y) : f.comp (norm_hom.id _) = f :=
norm_hom.rec_on_tt f (by intros; simp [comp]; refl) (by intros; simp [comp, *] at *)

lemma id_comp {X Y : prod_coprod C} (f : norm_hom tt X Y) : (norm_hom.id X).comp f = f := rfl

lemma comp_ff_comp {W X Y Z : prod_coprod C} (f : norm_hom ff W X) (g : norm_hom tt X Y) (h : norm_hom tt Y Z) :
  (f.comp_ff g).comp h = f.comp_ff (g.comp h) := rfl

lemma comp_assoc {W X Y Z : prod_coprod C} (f : norm_hom tt W X) (g : norm_hom tt X Y) (h : norm_hom tt Y Z) :
  (f.comp g).comp h = f.comp (g.comp h) :=
begin
  revert g h,
  refine norm_hom.rec_on_tt f _ _,
  { intros, refl },
  { intros,
    simp [comp_ff_comp, *] at * }
end

inductive rel : Π {X Y : prod_coprod C}, norm_hom tt X Y → norm_hom tt X Y → Prop
| refl {X Y : prod_coprod C} (f : norm_hom tt X Y) : rel f f
| symm {X Y : prod_coprod C} {f g : norm_hom tt X Y} : rel f g → rel g f
| trans {X Y : prod_coprod C} {f g h : norm_hom tt X Y} : rel f g → rel g h → rel f h
| comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom tt X Y} {g₁ g₂ : norm_hom tt Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp g₁) (f₂.comp g₂)
| prod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom tt X Y} {g₁ g₂ : norm_hom tt X Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.prod_mk g₁) (f₂.prod_mk g₂)
| coprod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : norm_hom tt X Z} {g₁ g₂ : norm_hom tt Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.coprod_mk g₁) (f₂.coprod_mk g₂)
| of_cat_id {X : C} : rel (norm_hom.of_cat (𝟙 X)) (norm_hom.id (of_cat' X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  rel (norm_hom.of_cat (f ≫ g)) (norm_hom.comp (norm_hom.of_cat f) (norm_hom.of_cat g))
| mk_comp_fst {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt X Z) :
  rel (norm_hom.comp (norm_hom.prod_mk f g) norm_hom.fst) f
| mk_comp_snd {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt X Z) :
  rel (norm_hom.comp (norm_hom.prod_mk f g) norm_hom.snd) g
| prod_eta {X Y Z : prod_coprod C} (f : norm_hom tt X (Y.prod Z)) :
  rel (norm_hom.prod_mk (f.comp norm_hom.fst) (f.comp norm_hom.snd)) f
| inl_comp_mk {X Y Z : prod_coprod C} (f : norm_hom tt X Z) (g : norm_hom tt Y Z) :
  rel (norm_hom.comp norm_hom.inl (norm_hom.coprod_mk f g)) f
| inr_comp_mk {X Y Z : prod_coprod C} (f : norm_hom tt X Z) (g : norm_hom tt Y Z) :
  rel (norm_hom.comp norm_hom.inr (norm_hom.coprod_mk f g)) g
| coprod_eta {X Y Z : prod_coprod C} (f : norm_hom tt (X.coprod Y) Z) :
  rel (norm_hom.coprod_mk (norm_hom.inl.comp f) (norm_hom.inr.comp f)) f

attribute [refl] rel.refl

inductive normal_form : Π {X Y : prod_coprod C} (f : norm_hom tt X Y), Prop
| of_cat {X Y : C}, normal_form _

def is_inl_or_inr_or_fst_or_snd : Π {X Y : prod_coprod C}
  (f : norm_hom tt X Y),
  { g : norm_hom tt (of_cat' X) Y // rel f (g.comp inl) } ⊕
  { g : norm_hom tt (of_cat' X) Z // rel f (g.comp inr) }
| _ _ _ (norm_hom.comp_ff inl_ff (norm_hom.id _)) :=
  sum.inl ⟨norm_hom.id _, by refl⟩
| _ _ _ (norm_hom.comp_ff inr_ff (norm_hom.id _)) :=
  sum.inr ⟨norm_hom.id _, by refl⟩

def is_inl_or_inr : Π {X : C} {Y Z : prod_coprod C} (f : norm_hom tt (of_cat' X) (Y.coprod Z)),
  { g : norm_hom tt (of_cat' X) Y // rel f (g.comp inl) } ⊕
  { g : norm_hom tt (of_cat' X) Z // rel f (g.comp inr) }
| _ _ _ (norm_hom.comp_ff inl_ff (norm_hom.id _)) :=
  sum.inl ⟨norm_hom.id _, by refl⟩
| _ _ _ (norm_hom.comp_ff inr_ff (norm_hom.id _)) :=
  sum.inr ⟨norm_hom.id _, by refl⟩



end norm_hom


inductive hom' : Π (X Y : prod_coprod C), Type
| of_cat {X Y : C} : (X ⟶ Y) → hom' (of_cat' X) (of_cat' Y)
| prod_mk {X Y Z : prod_coprod C} : hom' X Y → hom' X Z → hom' X (Y.prod Z)
| fst {X Y : prod_coprod C} : hom' (X.prod Y) X
| snd {X Y : prod_coprod C} : hom' (X.prod Y) Y
| coprod_mk {X Y Z : prod_coprod C} : hom' X Z → hom' Y Z → hom' (X.coprod Y) Z
| inl {X Y : prod_coprod C} : hom' X (X.coprod Y)
| inr {X Y : prod_coprod C} : hom' Y (X.coprod Y)
| id (X : prod_coprod C) : hom' X X
| comp {X Y Z : prod_coprod C} : hom' X Y → hom' Y Z → hom' X Z

inductive rel : Π {X Y : prod_coprod C}, hom' X Y → hom' X Y → Prop
| refl {X Y : prod_coprod C} (f : hom' X Y) : rel f f
| symm {X Y : prod_coprod C} {f g : hom' X Y} : rel f g → rel g f
| trans {X Y : prod_coprod C} {f g h : hom' X Y} : rel f g → rel g h → rel f h
| comp_congr {X Y Z : prod_coprod C} {f₁ f₂ : hom' X Y} {g₁ g₂ : hom' Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.comp g₁) (f₂.comp g₂)
| prod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : hom' X Y} {g₁ g₂ : hom' X Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.prod_mk g₁) (f₂.prod_mk g₂)
| coprod_mk_congr {X Y Z : prod_coprod C} {f₁ f₂ : hom' X Z} {g₁ g₂ : hom' Y Z} :
  rel f₁ f₂ → rel g₁ g₂ → rel (f₁.coprod_mk g₁) (f₂.coprod_mk g₂)
| of_cat_id {X : C} : rel (hom'.of_cat (𝟙 X)) (hom'.id (of_cat' X))
| of_cat_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
  rel (hom'.of_cat (f ≫ g)) (hom'.comp (hom'.of_cat f) (hom'.of_cat g))
| comp_id {X Y : prod_coprod C} (f : hom' X Y) : rel (hom'.comp f (hom'.id Y)) f
| id_comp {X Y : prod_coprod C} (f : hom' X Y) : rel (hom'.comp (hom'.id X) f) f
| comp_assoc {W X Y Z : prod_coprod C} (f : hom' W X) (g : hom' X Y) (h : hom' Y Z) :
  rel (hom'.comp (hom'.comp f g) h) (hom'.comp f (hom'.comp g h))
| mk_comp_fst {X Y Z : prod_coprod C} (f : hom' X Y) (g : hom' X Z) :
  rel (hom'.comp (hom'.prod_mk f g) hom'.fst) f
| mk_comp_snd {X Y Z : prod_coprod C} (f : hom' X Y) (g : hom' X Z) :
  rel (hom'.comp (hom'.prod_mk f g) hom'.snd) g
| prod_eta {X Y Z : prod_coprod C} (f : hom' X (Y.prod Z)) :
  rel (hom'.prod_mk (f.comp hom'.fst) (f.comp hom'.snd)) f
| inl_comp_mk {X Y Z : prod_coprod C} (f : hom' X Z) (g : hom' Y Z) :
  rel (hom'.comp hom'.inl (hom'.coprod_mk f g)) f
| inr_comp_mk {X Y Z : prod_coprod C} (f : hom' X Z) (g : hom' Y Z) :
  rel (hom'.comp hom'.inr (hom'.coprod_mk f g)) g
| coprod_eta {X Y Z : prod_coprod C} (f : hom' (X.coprod Y) Z) :
  rel (hom'.coprod_mk (hom'.inl.comp f) (hom'.inr.comp f)) f

attribute [refl] rel.refl
attribute [symm] rel.symm
attribute [trans] rel.trans

infixl ` ♥ `: 50 := rel

lemma rel_prod {X Y Z : prod_coprod C} {f g : hom' X (Y.prod Z)}
  (h₁ : rel (f.comp hom'.fst) (g.comp hom'.fst))
  (h₂ : rel (f.comp hom'.snd) (g.comp hom'.snd)) :
  rel f g :=
calc f ♥ hom'.prod_mk (f.comp hom'.fst) (f.comp hom'.snd) : rel.symm (rel.prod_eta f)
   ... ♥ hom'.prod_mk (g.comp hom'.fst) (g.comp hom'.snd) : rel.prod_mk_congr h₁ h₂
   ... ♥ g : rel.prod_eta g

lemma rel_coprod {X Y Z : prod_coprod C} {f g : hom' (X.coprod Y) Z}
  (h₁ : rel (hom'.inl.comp f) (hom'.inl.comp g))
  (h₂ : rel (hom'.inr.comp f) (hom'.inr.comp g)) :
  rel f g :=
calc f ♥ hom'.coprod_mk (hom'.inl.comp f) (hom'.inr.comp f) : rel.symm (rel.coprod_eta f)
   ... ♥ hom'.coprod_mk (hom'.inl.comp g) (hom'.inr.comp g) : rel.coprod_mk_congr h₁ h₂
   ... ♥ g : rel.coprod_eta g

instance rel_setoid (X Y : prod_coprod C) : setoid (hom' X Y) :=
{ r := rel,
  iseqv := ⟨rel.refl, λ _ _, rel.symm, λ _ _ _, rel.trans⟩ }

def hom (X Y : prod_coprod C) : Type := quotient (prod_coprod.rel_setoid X Y)

instance : category_struct (prod_coprod C) :=
{ hom := hom,
  id := λ X, quotient.mk' (hom'.id X),
  comp := λ X Y Z f g, quotient.lift_on₂ f g (λ f g, quotient.mk' (hom'.comp f g))
    (λ f₁ g₁ f₂ g₂ hf hg, quotient.sound (rel.comp_congr hf hg)) }

instance : category (prod_coprod C) :=
{ id_comp' := λ X Y f, quotient.induction_on f (λ f, quotient.sound (rel.id_comp f)),
  comp_id' := λ X Y f, quotient.induction_on f (λ f, quotient.sound (rel.comp_id f)),
  assoc' := λ W X Y Z f g h, quotient.induction_on₃ f g h
    (λ f g h, quotient.sound (rel.comp_assoc f g h)) }

def prod_mk {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) : X ⟶ (Y.prod Z) :=
quotient.lift_on₂ f g (λ f g, ⟦f.prod_mk g⟧)
  (λ f₁ g₁ f₂ g₂ h₁ h₂, quotient.sound (rel.prod_mk_congr h₁ h₂))

def fst {X Y : prod_coprod C} : (X.prod Y) ⟶ X :=
⟦hom'.fst⟧

def snd {X Y : prod_coprod C} : (X.prod Y) ⟶ Y :=
⟦hom'.snd⟧

def coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) : (X.coprod Y) ⟶ Z :=
quotient.lift_on₂ f g (λ f g, ⟦f.coprod_mk g⟧)
  (λ f₁ g₁ f₂ g₂ h₁ h₂, quotient.sound (rel.coprod_mk_congr h₁ h₂))

def inl {X Y : prod_coprod C} : X ⟶ (X.coprod Y) :=
⟦hom'.inl⟧

def inr {X Y : prod_coprod C} : Y ⟶ (X.coprod Y) :=
⟦hom'.inr⟧

def of_cat : C ⥤ prod_coprod C :=
{ obj := λ X, of_cat' X,
  map := λ X Y f, ⟦hom'.of_cat f⟧,
  map_id' := λ X, quotient.sound rel.of_cat_id,
  map_comp' := λ X Y Z f g, quotient.sound (rel.of_cat_comp f g) }

-- noncomputable def to_presheaf_obj : prod_coprod C → (Cᵒᵖ ⥤ Type)
-- | (of_cat' X) := yoneda.obj X
-- | (prod X Y) := to_presheaf_obj X ⨯ to_presheaf_obj Y
-- | (coprod X Y) := to_presheaf_obj X ⨿ to_presheaf_obj Y


@[simp] def Pprod (F G : C ⥤ Type) : C ⥤ Type :=
{ obj := λ X, F.obj X × G.obj X,
  map := λ X Y f, prod.map (F.map f) (G.map f) }

@[simp] def Pprod_lift {F G H : C ⥤ Type} (f : F ⟶ G) (g : F ⟶ H) : F ⟶ Pprod G H :=
{ app := λ X x, (f.app X x, g.app X x),
  naturality' := begin
    intros X Y n,
    have := f.naturality n,
    have := g.naturality n,
    simp only [function.funext_iff] at *,
    dsimp at *,
    intros,
    ext;
    simp *,
  end }

@[simp] def Pprod_fst {F G : C ⥤ Type} : Pprod F G ⟶ F :=
{ app := λ X x, x.fst,
  naturality' := begin
    tidy
  end }

@[simp] def Pprod_snd {F G : C ⥤ Type} : Pprod F G ⟶ G :=
{ app := λ X x, x.snd,
  naturality' := begin
    tidy
  end }

@[simp] def Pcoprod (F G : C ⥤ Type) : C ⥤ Type :=
{ obj := λ X, F.obj X ⊕ G.obj X,
  map := λ X Y f, sum.map (F.map f) (G.map f) }

@[simp] def Pcoprod_lift {F G H : C ⥤ Type} (f : F ⟶ H) (g : G ⟶ H) : Pcoprod F G ⟶ H :=
{ app := λ X x, sum.cases_on x (f.app X) (g.app X),
  naturality' := begin
    intros X Y n,
    have := f.naturality n,
    have := g.naturality n,
    simp only [function.funext_iff] at *,
    dsimp at *,
    intros x,
    cases x; dsimp; simp [*, sum.map]
  end }

@[simp] def Pcoprod_inl {F G : C ⥤ Type} : F ⟶ Pcoprod F G :=
{ app := λ X x, sum.inl x,
  naturality' := begin
    tidy
  end }

@[simp] def Pcoprod_inr {F G : C ⥤ Type} : G ⟶ Pcoprod F G :=
{ app := λ X x, sum.inr x,
  naturality' := begin
    tidy
  end }

noncomputable def to_presheaf_obj (X : prod_coprod C) : (Cᵒᵖ ⥤ Type) :=
prod_coprod.rec_on X
  yoneda.obj
  (λ X Y ih₁ ih₂, Pprod ih₁ ih₂)
  (λ X Y ih₁ ih₂, Pcoprod ih₁ ih₂)

@[simp] noncomputable def to_presheaf_hom' : Π {X Y : prod_coprod C}, hom' X Y →
  ((to_presheaf_obj X) ⟶ (to_presheaf_obj Y))
| _ _ (hom'.of_cat f) := yoneda.map f
| X _ (hom'.prod_mk f g) := Pprod_lift (to_presheaf_hom' f) (to_presheaf_hom' g)
| _ _ (hom'.fst) := Pprod_fst
| _ _ (hom'.snd) := Pprod_snd
| _ _ (hom'.coprod_mk f g) := Pcoprod_lift (to_presheaf_hom' f) (to_presheaf_hom' g)
| _ _ (hom'.inl) := Pcoprod_inl
| _ _ (hom'.inr) := Pcoprod_inr
| _ _ (hom'.id X) := 𝟙 _
| _ _ (hom'.comp f g) := to_presheaf_hom' f ≫ to_presheaf_hom' g

lemma to_presheaf_hom'_rel {X Y : prod_coprod C} (f g : hom' X Y) (h : rel f g) :
  to_presheaf_hom' f = to_presheaf_hom' g :=
begin
  induction h,
  { refl },
  { symmetry, assumption },
  { transitivity, assumption, assumption },
  { simp * },
  { simp * },
  { simp * },
  { simp, refl },
  { simp },
  { simp },
  { simp },
  { simp },
  { tidy },
  { tidy },
  { ext; simp },
  { tidy },
  { tidy },
  { tidy }
end

def to_presheaf : prod_coprod C ⥤ (Cᵒᵖ ⥤ Type) :=
{ obj := to_presheaf_obj,
  map := λ X Y f, quotient.lift_on f (to_presheaf_hom') to_presheaf_hom'_rel,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ f g, quotient.induction_on₂ f g begin intros, simp,
    erw quotient.lift_on_mk,
    simp end }

@[simp] lemma to_presheaf_obj_of_cat (X : C) : to_presheaf.obj (of_cat' X) = yoneda.obj X := rfl
@[simp] lemma to_presheaf_obj_prod (X Y : prod_coprod C) : to_presheaf.obj (prod X Y) =
  Pprod (to_presheaf.obj X) (to_presheaf.obj Y) := rfl
@[simp] lemma to_presheaf_obj_coprod (X Y : prod_coprod C) : to_presheaf.obj (coprod X Y) =
  Pcoprod (to_presheaf.obj X) (to_presheaf.obj Y) := rfl

lemma to_presheaf_faithful : Π {X Y : prod_coprod C} (f g : hom' X Y)
  (h : to_presheaf_hom' f = to_presheaf_hom' g), rel f g
| X (prod Y Z) f g h := rel_prod
  (to_presheaf_faithful _ _ begin
    dsimp [to_presheaf_hom'],
    rw h
  end)
  (to_presheaf_faithful _ _ begin
    dsimp [to_presheaf_hom'],
    rw h
  end)
| (coprod X Y) Z f g h := rel_coprod
  (to_presheaf_faithful _ _ begin
    dsimp [to_presheaf_hom'],
    rw h
  end)
  (to_presheaf_faithful _ _ begin
    dsimp [to_presheaf_hom'],
    rw h
  end)
| (of_cat' _) (of_cat' _) _ _ _ := sorry
| (of_cat' _) (coprod _ _) _ _ _ := sorry
| (prod _ _) (of_cat' _) _ _ _ := sorry
| (prod _ _) (coprod _ _) _ _ _ := sorry

def reverse_map2 : Π {X : C} {Y : prod_coprod C}, ((to_presheaf.obj (of_cat' X)) ⟶ (to_presheaf.obj Y)) →
  (of_cat' X ⟶ Y)
| X (of_cat' Y) := λ f, of_cat.map (yoneda.preimage f)
| X (prod Y Z) := λ f, prod_mk (reverse_map2 (f ≫ Pprod_fst)) (reverse_map2 (f ≫ Pprod_snd))
| X (coprod Y Z) := λ f, begin
  cases f,
  dsimp [sum.map] at *,
  have := f_app (opposite.op X) (𝟙 _),
  cases this,
  { have h2 := @reverse_map2 X Y,
    have := h2 (yoneda_equiv.2 this),
    exact this ≫ inl },
  { have h2 := @reverse_map2 X Z,
    have := h2 (yoneda_equiv.2 this),
    exact this ≫ inr }

def reverse_map : Π {X Y : prod_coprod C}, ((to_presheaf.obj X) ⟶ (to_presheaf.obj Y)) → (X ⟶ Y)
| (of_cat' X) (of_cat' Y) := λ f, of_cat.map (yoneda.preimage f)
| X (prod Y Z) := λ f, prod_mk (reverse_map (f ≫ Pprod_fst)) (reverse_map (f ≫ Pprod_snd))
| (coprod X Y) Z := λ f, coprod_mk (reverse_map (Pcoprod_inl ≫ f)) (reverse_map (Pcoprod_inr ≫ f))
| (of_cat' X) (of_cat' Z) := λ f, of_cat.map (yoneda.preimage f)
| (prod X Y) (of_cat' Z) := λ f, begin
  cases f,
  have := f_app,
  have := @reverse_map X (of_cat' Z),
  have := @reverse_map Y (of_cat' Z),
  dsimp at *,

end


end prod_coprod