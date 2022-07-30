import category_theory.yoneda

open category_theory

universes u v

variables {C : Type u} [category.{v} C]

@[simps] def Pprod (F G : C ⥤ Type) : C ⥤ Type :=
{ obj := λ X, F.obj X × G.obj X,
  map := λ X Y f, prod.map (F.map f) (G.map f) }

@[simps] def Pprod_lift {F G H : C ⥤ Type} (f : F ⟶ G) (g : F ⟶ H) : F ⟶ Pprod G H :=
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

@[simps] def Pprod_fst {F G : C ⥤ Type} : Pprod F G ⟶ F :=
{ app := λ X x, x.fst,
  naturality' := begin
    tidy
  end }

@[simps] def Pprod_snd {F G : C ⥤ Type} : Pprod F G ⟶ G :=
{ app := λ X x, x.snd,
  naturality' := begin
    tidy
  end }

@[simp] lemma Pprod_lift_comp_fst {F G H : C ⥤ Type} (f : F ⟶ G) (g : F ⟶ H) :
  Pprod_lift f g ≫ Pprod_fst = f := by ext; refl

@[simp] lemma Pprod_lift_comp_snd {F G H : C ⥤ Type} (f : F ⟶ G) (g : F ⟶ H) :
  Pprod_lift f g ≫ Pprod_snd = g := by ext; refl

@[simps] def Pcoprod (F G : C ⥤ Type) : C ⥤ Type :=
{ obj := λ X, F.obj X ⊕ G.obj X,
  map := λ X Y f, sum.map (F.map f) (G.map f) }

@[simps] def Pcoprod_lift {F G H : C ⥤ Type} (f : F ⟶ H) (g : G ⟶ H) : Pcoprod F G ⟶ H :=
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

@[simps] def Pcoprod_inl {F G : C ⥤ Type} : F ⟶ Pcoprod F G :=
{ app := λ X x, sum.inl x,
  naturality' := begin
    tidy
  end }

@[simps] def Pcoprod_inr {F G : C ⥤ Type} : G ⟶ Pcoprod F G :=
{ app := λ X x, sum.inr x,
  naturality' := begin
    tidy
  end }


@[simp] lemma inl_comp_Pcoprod_lift {F G H : C ⥤ Type} (f : F ⟶ H) (g : G ⟶ H) :
  Pcoprod_inl ≫ Pcoprod_lift f g = f := by ext; refl

@[simp] lemma inr_comp_Pcoprod_lift {F G H : C ⥤ Type} (f : F ⟶ H) (g : G ⟶ H) :
  Pcoprod_inr ≫ Pcoprod_lift f g = g := by ext; refl
