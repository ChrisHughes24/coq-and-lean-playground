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

inductive norm_hom : bool → Π (X Y : prod_coprod C), Type
| of_cat_ff {X Y : C} : (X ⟶ Y) → norm_hom ff (of_cat' X) (of_cat' Y)
| prod_mk_ff {X Y Z : prod_coprod C} : norm_hom tt X Y → norm_hom tt X Z → norm_hom ff X (Y.prod Z)
| fst_ff {X Y : prod_coprod C} : norm_hom ff (X.prod Y) X
| snd_ff {X Y : prod_coprod C} : norm_hom ff (X.prod Y) Y
| coprod_mk_ff {X Y Z : prod_coprod C} : norm_hom tt X Z → norm_hom tt Y Z → norm_hom ff (X.coprod Y) Z
| inl_ff {X Y : prod_coprod C} : norm_hom ff X (X.coprod Y)
| inr_ff {X Y : prod_coprod C} : norm_hom ff Y (X.coprod Y)
| id (X : prod_coprod C) : norm_hom tt X X
| comp_ff {X Y Z : prod_coprod C} : norm_hom tt X Y → norm_hom ff Y Z → norm_hom tt X Z

namespace norm_hom

@[simp] def of_ff {X Y : prod_coprod C} (f : norm_hom ff X Y) : norm_hom tt X Y :=
norm_hom.comp_ff (norm_hom.id _) f

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

@[elab_as_eliminator] def norm_hom.rec_on_ff {motive : ∀ X Y : prod_coprod C, norm_hom ff X Y → Sort*}
  {X Y : prod_coprod C} (f : norm_hom ff X Y)
  (h₁ : ∀ (X Y : C) (f : X ⟶ Y), motive _ _ (norm_hom.of_cat_ff f))
  (h₂ : ∀ (X Y Z : prod_coprod C) (f : norm_hom tt X Y) (g : norm_hom tt X Z),
    motive _ _ (prod_mk_ff f g))
  (h₃ : ∀ (X Y : prod_coprod C), motive (X.prod Y) X fst_ff)
  (h₃ : ∀ (X Y : prod_coprod C), motive (X.prod Y) Y snd_ff)
  (h₄ : ∀ (X Y Z : prod_coprod C) (f : norm_hom tt X Z) (g : norm_hom tt Y Z),
    motive _ _ (coprod_mk_ff f g))
  (h₅ : ∀ (X Y : prod_coprod C), motive X (X.coprod Y) inl_ff)
  (h₆ : ∀ (X Y : prod_coprod C), motive Y (X.coprod Y) inr_ff) :
  motive X Y f :=
have ∀ (b : bool) (f : norm_hom b X Y) (h : b = ff), motive X Y (eq.rec_on h f),
  from λ b f, begin
    induction f; intros; tauto,
  end,
this ff f rfl

@[elab_as_eliminator] def norm_hom.rec_on_tt {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X Y : prod_coprod C} (f : norm_hom tt X Y)
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom tt X Y) (g : norm_hom ff Y Z), motive X Y f →
    motive X Z (f.comp_ff g)) :
  motive X Y f :=
have ∀ (b : bool) (f : norm_hom b X Y) (h : b = tt), motive X Y (eq.rec_on h f),
  from λ b f, begin
    induction f; try {intros; tauto},
    { intros h, apply h₂,
      tauto }
  end,
this tt f rfl


@[simp] lemma norm_hom.rec_on_tt_id  {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X : prod_coprod C}
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom tt X Y) (g : norm_hom ff Y Z), motive X Y f →
    motive X Z (f.comp_ff g)) :
  @norm_hom.rec_on_tt C _ motive X X (norm_hom.id X) h₁ h₂ = h₁ X := rfl

@[simp] lemma norm_hom.rec_on_tt_comp_ff {motive : ∀ X Y : prod_coprod C, norm_hom tt X Y → Sort*}
  {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom ff Y Z)
  (h₁ : ∀ X, motive X X (norm_hom.id X))
  (h₂ : ∀ X Y Z (f : norm_hom tt X Y) (g : norm_hom ff Y Z), motive X Y f →
    motive X Z (f.comp_ff g)) :
  @norm_hom.rec_on_tt C _ motive X Z (norm_hom.comp_ff f g) h₁ h₂ = h₂ X Y Z f g
    (@norm_hom.rec_on_tt C _ motive X Y f h₁ h₂) := rfl

def comp {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt Y Z) : norm_hom tt X Z :=
norm_hom.rec_on_tt g (λ _ f, f) (λ _ _ _ f f ih g, norm_hom.comp_ff (ih g) f) f

lemma comp_id {X Y : prod_coprod C} (f : norm_hom tt X Y) : f.comp (norm_hom.id _) = f := rfl

lemma id_comp {X Y : prod_coprod C} (f : norm_hom tt X Y) : (norm_hom.id X).comp f = f :=
norm_hom.rec_on_tt f (by intros; simp [comp]; refl) (by intros; simp [comp, *] at *)

lemma comp_comp_ff {W X Y Z : prod_coprod C} (f : norm_hom tt W X) (g : norm_hom tt X Y) (h : norm_hom ff Y Z) :
  f.comp (g.comp_ff h) = (f.comp g).comp_ff h := rfl

lemma comp_assoc {W X Y Z : prod_coprod C} (f : norm_hom tt W X) (g : norm_hom tt X Y) (h : norm_hom tt Y Z) :
  (f.comp g).comp h = f.comp (g.comp h) :=
begin
  revert f g,
  refine norm_hom.rec_on_tt h _ _,
  { intros, refl },
  { intros,
    simp [comp_comp_ff, *] at * }
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
attribute [symm] rel.symm
attribute [trans] rel.trans

infixl ` ♥ `: 50 := rel

lemma rel_prod {X Y Z : prod_coprod C} {f g : norm_hom tt X (Y.prod Z)}
  (h₁ : rel (f.comp norm_hom.fst) (g.comp norm_hom.fst))
  (h₂ : rel (f.comp norm_hom.snd) (g.comp norm_hom.snd)) :
  rel f g :=
calc f ♥ norm_hom.prod_mk (f.comp norm_hom.fst) (f.comp norm_hom.snd) : rel.symm (rel.prod_eta f)
   ... ♥ norm_hom.prod_mk (g.comp norm_hom.fst) (g.comp norm_hom.snd) : rel.prod_mk_congr h₁ h₂
   ... ♥ g : rel.prod_eta g

lemma rel_coprod {X Y Z : prod_coprod C} {f g : norm_hom tt (X.coprod Y) Z}
  (h₁ : rel (norm_hom.inl.comp f) (norm_hom.inl.comp g))
  (h₂ : rel (norm_hom.inr.comp f) (norm_hom.inr.comp g)) :
  rel f g :=
calc f ♥ norm_hom.coprod_mk (norm_hom.inl.comp f) (norm_hom.inr.comp f) : rel.symm (rel.coprod_eta f)
   ... ♥ norm_hom.coprod_mk (norm_hom.inl.comp g) (norm_hom.inr.comp g) : rel.coprod_mk_congr h₁ h₂
   ... ♥ g : rel.coprod_eta g

instance rel_setoid (X Y : prod_coprod C) : setoid (norm_hom tt X Y) :=
{ r := rel,
  iseqv := ⟨rel.refl, λ _ _, rel.symm, λ _ _ _, rel.trans⟩ }

end norm_hom

section norm_hom

open norm_hom

def hom (X Y : prod_coprod C) : Type := quotient (norm_hom.rel_setoid X Y)

instance : category_struct (prod_coprod C) :=
{ hom := hom,
  id := λ X, quotient.mk' (norm_hom.id X),
  comp := λ X Y Z f g, quotient.lift_on₂ f g (λ f g, quotient.mk' (norm_hom.comp f g))
    (λ f₁ g₁ f₂ g₂ hf hg, quotient.sound (rel.comp_congr hf hg)) }

instance : category (prod_coprod C) :=
{ id_comp' := λ X Y f, quotient.induction_on f (λ f, congr_arg quotient.mk (id_comp _)),
  comp_id' := λ X Y f, quotient.induction_on f (λ f, congr_arg quotient.mk (comp_id _)),
  assoc' := λ W X Y Z f g h, quotient.induction_on₃ f g h
    (λ f g h, congr_arg quotient.mk (comp_assoc _ _ _)) }

def of_cat : C ⥤ prod_coprod C :=
{ obj := λ X, of_cat' X,
  map := λ X Y f, ⟦norm_hom.of_cat f⟧,
  map_id' := λ X, quotient.sound rel.of_cat_id,
  map_comp' := λ X Y Z f g, quotient.sound (rel.of_cat_comp f g) }

@[simp] lemma of_cat_obj (X : C) : of_cat.obj X = of_cat' X := rfl

def to_presheaf_obj (X : prod_coprod C) : (Cᵒᵖ ⥤ Type) :=
prod_coprod.rec_on X
  yoneda.obj
  (λ X Y ih₁ ih₂, Pprod ih₁ ih₂)
  (λ X Y ih₁ ih₂, Pcoprod ih₁ ih₂)

-- | of_cat_ff {X Y : C} : (X ⟶ Y) → norm_hom ff (of_cat' X) (of_cat' Y)
-- | prod_mk_ff {X Y Z : prod_coprod C} : norm_hom tt X Y → norm_hom tt X Z → norm_hom ff X (Y.prod Z)
-- | fst_ff {X Y : prod_coprod C} : norm_hom ff (X.prod Y) X
-- | snd_ff {X Y : prod_coprod C} : norm_hom ff (X.prod Y) Y
-- | coprod_mk_ff {X Y Z : prod_coprod C} : norm_hom tt X Z → norm_hom tt Y Z → norm_hom ff (X.coprod Y) Z
-- | inl_ff {X Y : prod_coprod C} : norm_hom ff X (X.coprod Y)
-- | inr_ff {X Y : prod_coprod C} : norm_hom ff Y (X.coprod Y)
-- | id (X : prod_coprod C) : norm_hom tt X X
-- | comp_ff {X Y Z : prod_coprod C} : norm_hom tt X Y → norm_hom ff Y Z → norm_hom tt X Z

def of_norm_hom_tt {X Y : prod_coprod C} (f : norm_hom tt X Y) : X ⟶ Y :=
⟦f⟧

def of_norm_hom_ff {X Y : prod_coprod C} (f : norm_hom ff X Y) : X ⟶ Y :=
of_norm_hom_tt (norm_hom.of_ff f)

def of_norm_hom_bool {X Y : prod_coprod C} {b : bool} (f : norm_hom b X Y) : X ⟶ Y :=
match b, f with
| tt, f := of_norm_hom_tt f
| ff, f := of_norm_hom_ff f
end

def prod_mk {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) : X ⟶ (Y.prod Z) :=
quotient.lift_on₂ f g (λ f g, of_norm_hom_tt (prod_mk f g)) begin
  intros,
  dsimp,
  refine quotient.sound _,
  refine rel.prod_mk_congr _ _; assumption
end

def fst {X Y : prod_coprod C} : (X.prod Y) ⟶ X :=
of_norm_hom_tt fst

def snd {X Y : prod_coprod C} : (X.prod Y) ⟶ Y :=
of_norm_hom_tt snd

@[simp] lemma prod_mk_comp_fst {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ fst = f :=
quotient.induction_on₂ f g (λ f g, quotient.sound (norm_hom.rel.mk_comp_fst _ _))

@[simp] lemma prod_mk_comp_snd {X Y Z : prod_coprod C} (f : X ⟶ Y) (g : X ⟶ Z) :
  prod_mk f g ≫ snd = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (norm_hom.rel.mk_comp_snd _ _))

lemma prod_mk_eta {X Y Z : prod_coprod C} (f : X ⟶ Y.prod Z) :
  prod_mk (f ≫ fst) (f ≫ snd) = f :=
quotient.induction_on f (λ f, quotient.sound (norm_hom.rel.prod_eta _))

lemma prod_hom_ext {X Y Z : prod_coprod C} {f g : X ⟶ Y.prod Z}
  (h₁ : f ≫ fst = g ≫ fst) (h₂ : f ≫ snd = g ≫ snd) : f = g :=
begin
  conv_lhs { rw ← prod_mk_eta f },
  rw [h₁, h₂, prod_mk_eta]
end

def coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) : (X.coprod Y) ⟶ Z :=
quotient.lift_on₂ f g (λ f g, of_norm_hom_tt (coprod_mk f g)) begin
  intros,
  dsimp,
  refine quotient.sound _,
  refine rel.coprod_mk_congr _ _; assumption
end

def inl {X Y : prod_coprod C} : X ⟶ (X.coprod Y) :=
of_norm_hom_tt inl

def inr {X Y : prod_coprod C} : Y ⟶ (X.coprod Y) :=
of_norm_hom_tt inr

@[simp] lemma inl_comp_coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inl ≫ coprod_mk f g = f :=
quotient.induction_on₂ f g (λ f g, quotient.sound (norm_hom.rel.inl_comp_mk _ _))

@[simp] lemma inr_comp_coprod_mk {X Y Z : prod_coprod C} (f : X ⟶ Z) (g : Y ⟶ Z) :
  inr ≫ coprod_mk f g = g :=
quotient.induction_on₂ f g (λ f g, quotient.sound (norm_hom.rel.inr_comp_mk _ _))

lemma coprod_mk_eta {X Y Z : prod_coprod C} (f : X.coprod Y ⟶ Z) :
  coprod_mk (inl ≫ f) (inr ≫ f) = f :=
quotient.induction_on f (λ f, quotient.sound (norm_hom.rel.coprod_eta _))

lemma coprod_hom_ext {X Y Z : prod_coprod C} {f g : X.coprod Y ⟶ Z}
  (h₁ : inl ≫ f = inl ≫ g ) (h₂ : inr ≫ f = inr ≫ g) : f = g :=
begin
  conv_lhs { rw ← coprod_mk_eta f },
  rw [h₁, h₂, coprod_mk_eta]
end

@[simp] lemma of_norm_hom_tt_of_cat {X Y : C} (f : X ⟶ Y) :
  of_norm_hom_tt (norm_hom.of_cat f) = of_cat.map f := rfl

@[simp] lemma of_norm_hom_ff_prod_mk_ff {X Y Z : prod_coprod C}
  (f : norm_hom tt X Y) (g : norm_hom tt X Z) : of_norm_hom_ff (prod_mk_ff f g) =
    prod_mk (of_norm_hom_tt f) (of_norm_hom_tt g) := rfl

@[simp] lemma of_norm_hom_tt_prod_mk {X Y Z : prod_coprod C}
  (f : norm_hom tt X Y) (g : norm_hom tt X Z) : of_norm_hom_tt (norm_hom.prod_mk f g) =
    prod_mk (of_norm_hom_tt f) (of_norm_hom_tt g) := rfl

@[simp] lemma of_norm_hom_ff_fst {X Y : prod_coprod C} :
  of_norm_hom_ff (fst_ff) = (fst : (X.prod Y) ⟶ X) := rfl

@[simp] lemma of_norm_hom_ff_snd {X Y : prod_coprod C} :
  of_norm_hom_ff (snd_ff) = (snd : (X.prod Y) ⟶ Y) := rfl

@[simp] lemma of_norm_hom_tt_fst {X Y : prod_coprod C} :
  of_norm_hom_tt norm_hom.fst = (fst : (X.prod Y) ⟶ X) := rfl

@[simp] lemma of_norm_hom_tt_snd {X Y : prod_coprod C} :
  of_norm_hom_tt norm_hom.snd = (snd : (X.prod Y) ⟶ Y) := rfl

@[simp] lemma of_norm_hom_ff_coprod_mk_ff {X Y Z : prod_coprod C}
  (f : norm_hom tt X Z) (g : norm_hom tt Y Z) : of_norm_hom_ff (coprod_mk_ff f g) =
    coprod_mk (of_norm_hom_tt f) (of_norm_hom_tt g) := rfl

@[simp] lemma of_norm_hom_tt_coprod_mk_ff {X Y Z : prod_coprod C}
  (f : norm_hom tt X Z) (g : norm_hom tt Y Z) : of_norm_hom_tt (norm_hom.coprod_mk f g) =
    coprod_mk (of_norm_hom_tt f) (of_norm_hom_tt g) := rfl

@[simp] lemma of_norm_hom_ff_inl {X Y : prod_coprod C} :
  of_norm_hom_ff (inl_ff) = (inl : X ⟶ (X.coprod Y)) := rfl

@[simp] lemma of_norm_hom_ff_inr {X Y : prod_coprod C} :
  of_norm_hom_ff (inr_ff) = (inr : Y ⟶ (X.coprod Y)) := rfl

@[simp] lemma of_norm_hom_tt_inl {X Y : prod_coprod C} :
  of_norm_hom_tt norm_hom.inl = (inl : X ⟶ (X.coprod Y)) := rfl

@[simp] lemma of_norm_hom_tt_inr {X Y : prod_coprod C} :
  of_norm_hom_tt norm_hom.inr = (inr : Y ⟶ (X.coprod Y)) := rfl

@[simp] lemma of_norm_hom_tt_comp_ff {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom ff Y Z) :
  of_norm_hom_tt (f.comp_ff g) = of_norm_hom_tt f ≫ of_norm_hom_ff g := rfl

@[simp] lemma of_norm_hom_tt_comp {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt Y Z) :
  of_norm_hom_tt (f.comp g) = of_norm_hom_tt f ≫ of_norm_hom_tt g := rfl

@[simp] lemma of_norm_hom_tt_id {X: prod_coprod C} :
  of_norm_hom_tt (norm_hom.id X) = 𝟙 X := rfl

@[simp] lemma of_norm_hom_ff_of_cat_ff {X Y : C} (f : X ⟶ Y) :
  of_norm_hom_ff (of_cat_ff f) = of_cat.map f := rfl

@[simp] lemma to_presheaf_obj_of_cat' (X : C) : to_presheaf_obj (of_cat' X) = yoneda.obj X := rfl
@[simp] lemma to_presheaf_obj_prod' (X Y : prod_coprod C) : to_presheaf_obj (prod X Y) =
  Pprod (to_presheaf_obj X) (to_presheaf_obj Y) := rfl
@[simp] lemma to_presheaf_obj_coprod' (X Y : prod_coprod C) : to_presheaf_obj (coprod X Y) =
  Pcoprod (to_presheaf_obj X) (to_presheaf_obj Y) := rfl

@[simp] def to_presheaf_norm_hom : Π {b : bool} {X Y : prod_coprod C}, norm_hom b X Y →
  ((to_presheaf_obj X) ⟶ (to_presheaf_obj Y))
| _ _ _ (norm_hom.of_cat_ff f) := yoneda.map f
| _ _ _ (norm_hom.prod_mk_ff f g) := Pprod_lift (to_presheaf_norm_hom f) (to_presheaf_norm_hom g)
| _ _ _ (norm_hom.fst_ff) := Pprod_fst
| _ _ _ (norm_hom.snd_ff) := Pprod_snd
| _ _ _ (norm_hom.coprod_mk_ff f g) := Pcoprod_lift (to_presheaf_norm_hom f) (to_presheaf_norm_hom g)
| _ _ _ (norm_hom.inl_ff) := Pcoprod_inl
| _ _ _ (norm_hom.inr_ff) := Pcoprod_inr
| _ _ _ (norm_hom.id X) := 𝟙 _
| _ _ _ (norm_hom.comp_ff f g) := to_presheaf_norm_hom f ≫ to_presheaf_norm_hom g

lemma to_presheaf_norm_hom_comp {X Y Z : prod_coprod C} (f : norm_hom tt X Y) (g : norm_hom tt Y Z) :
  to_presheaf_norm_hom (f.comp g) = to_presheaf_norm_hom f ≫ to_presheaf_norm_hom g :=
norm_hom.rec_on_tt g (by intros; simp [norm_hom.comp]) (by intros; simp [norm_hom.comp_comp_ff, *]) f

lemma to_presheaf_norm_hom_rel {X Y : prod_coprod C} (f g : norm_hom tt X Y) (h : rel f g) :
  to_presheaf_norm_hom f = to_presheaf_norm_hom g :=
begin
  induction h,
  { refl },
  { symmetry, assumption },
  { transitivity, assumption, assumption },
  { simp [*, to_presheaf_norm_hom_comp] },
  { simp [*, norm_hom.prod_mk] },
  { simp [*, norm_hom.coprod_mk] },
  { simp [norm_hom.of_cat], refl },
  { simp [norm_hom.of_cat, norm_hom.comp], },
  { ext,
    simp [norm_hom.prod_mk, norm_hom.comp, norm_hom.fst] },
  { ext,
    simp [norm_hom.prod_mk, norm_hom.comp, norm_hom.snd] },
  { ext;
    dsimp [norm_hom.prod_mk, norm_hom.comp, norm_hom.snd, norm_hom.fst];
    refl },
  { tidy },
  { tidy },
  { ext _ y,
    cases y;
    simp [norm_hom.coprod_mk, norm_hom.of_ff, to_presheaf_norm_hom_comp,
      norm_hom.inl, norm_hom.inr] },
end

def to_presheaf : prod_coprod C ⥤ (Cᵒᵖ ⥤ Type) :=
{ obj := to_presheaf_obj,
  map := λ X Y f, quotient.lift_on f (to_presheaf_norm_hom) to_presheaf_norm_hom_rel,
  map_id' := λ _, rfl,
  map_comp' := λ _ _ _ f g, quotient.induction_on₂ f g begin intros, simp,
    erw quotient.lift_on_mk,
    simp [to_presheaf_norm_hom_comp] end }

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

end norm_hom

def reverse_map : Π {X : C} {Y : prod_coprod C}, (to_presheaf.obj Y).obj (opposite.op X) →
  norm_hom tt (of_cat' X) Y
| X (of_cat' Y) := λ f, norm_hom.of_cat f
| X (prod Y Z) := λ f, norm_hom.prod_mk (reverse_map f.1) (reverse_map f.2)
| X (coprod Y Z) := λ f, f.elim
  (λ f, (reverse_map f).comp norm_hom.inl)
  (λ f, (reverse_map f).comp norm_hom.inr)

lemma reverse_map_to_presheaf : Π {X Y : prod_coprod C} {b : bool}
  (f : norm_hom b X Y) ⦃Z : C⦄ (z : (to_presheaf.obj X).obj (op Z)),
  of_norm_hom_tt (reverse_map ((to_presheaf.map (of_norm_hom_bool f)).app (op Z) z)) =
  of_norm_hom_tt (reverse_map z) ≫ of_norm_hom_bool f
| _ _ _ (norm_hom.of_cat_ff f) _ _ := by simp [reverse_map, of_norm_hom_bool]
| _ _ _ (norm_hom.prod_mk_ff f g) _ z := begin
  have := reverse_map_to_presheaf f z,
  have := reverse_map_to_presheaf g z,
  clear_aux_decl,
  apply prod_hom_ext;
  simp [reverse_map, of_norm_hom_bool, *] at *
end
| _ _ _ (norm_hom.coprod_mk_ff f g) _ z := begin
  have hf := reverse_map_to_presheaf f,
  have hg := reverse_map_to_presheaf g,
  simp [reverse_map, of_norm_hom_bool] at hf hg ⊢,
  cases z; simp *,
end
| _ _ _ norm_hom.fst_ff _ z := begin
  simp [reverse_map, of_norm_hom_bool]
end
| _ _ _ norm_hom.snd_ff _ z := begin
  simp [reverse_map, of_norm_hom_bool]
end
| _ _ _ norm_hom.inl_ff _ z := begin
  simp [reverse_map, of_norm_hom_bool]
end
| _ _ _ norm_hom.inr_ff _ z := begin
  simp [reverse_map, of_norm_hom_bool]
end
| _ _ _ (norm_hom.id _) _ z := begin
  simp [reverse_map, of_norm_hom_bool]
end
| X Y _ (@norm_hom.comp_ff _ _ _ Z _ f g) _ _ := begin
  have hf := reverse_map_to_presheaf f,
  have hg := reverse_map_to_presheaf g,
  simp [reverse_map, of_norm_hom_bool] at hf hg ⊢,
  rw [hg, hf, category.assoc],
end

instance of_cat_full : full (@of_cat C _) :=
{ preimage := λ X Y f, ((to_presheaf.map f).app (op X) (𝟙 X)),
  witness' := begin
    intros X Y f,
    refine quotient.induction_on f _,
    intro f,
    dsimp,
    have := reverse_map_to_presheaf f (𝟙 X),
    dsimp [reverse_map] at this,
    simp at this,
    erw [category.id_comp] at this,
    exact this
  end }
#print axioms prod_coprod.of_cat_full
end prod_coprod