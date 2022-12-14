import category_theory.adjunction.basic
import category_theory.limits.preserves.basic
import data.pfun

open category_theory category_theory.functor category_theory.limits
universes u v
variables (𝒞 : Type) [category.{0} 𝒞]

inductive bicompletion_aux : bool → Type 1
| of_cat_obj : 𝒞 → bicompletion_aux ff
| limit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| colimit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) : bicompletion_aux ff
| of_cat_hom : Π {X Y : 𝒞}, (X ⟶ Y) → bicompletion_aux tt -- of_cat_obj X ⟶ of_cat_obj Y
| limit_cone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt)
  (X : 𝒟) (Y : bicompletion_aux ff) (f : bicompletion_aux tt) : -- F_obj X ⟶ Y
  bicompletion_aux tt -- limit_obj F_obj F_hom ⟶ Y
| is_limit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt)
  (cone_obj : bicompletion_aux ff)
  (cone : Π (X : 𝒟), bicompletion_aux tt) : -- cone_obj ⟶ F_obj X
  bicompletion_aux tt -- cone_obj → limit_obj F_obj F_hom
| colimit_cocone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (X : 𝒟) (Y : bicompletion_aux ff) (f : bicompletion_aux tt) : -- Y ⟶ F_obj X
  bicompletion_aux tt -- Y ⟶ colimit_obj F_obj F_hom
| is_colimit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux ff) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux tt) 
  (cocone_obj : bicompletion_aux ff)
  (cocone : Π (X : 𝒟), bicompletion_aux tt) : -- F_obj X ⟶ cocone_obj
  bicompletion_aux tt -- colimit_obj F_obj F_hom ⟶ cocone_obj

namespace bicompletion_aux

variable {𝒞}

@[simp] def dom : Π (X : bicompletion_aux 𝒞 tt), bicompletion_aux 𝒞 ff
| (@of_cat_hom _ _ X Y f) := of_cat_obj X 
| (@limit_cone_comp _ _ 𝒟 _ F_obj F_hom X _ _) := by exactI limit_obj F_obj @F_hom
| (@is_limit _ _ 𝒟 _ F_obj F_hom cone_obj cone) := cone_obj
| (@colimit_cocone_comp _ _ 𝒟 _ F_obj F_hom X Y f) := Y
| (@is_colimit _ _ 𝒟 _ F_obj F_hom cocone_obj cocone) := by exactI colimit_obj F_obj @F_hom

@[simp] def cod : Π (X : bicompletion_aux 𝒞 tt), bicompletion_aux 𝒞 ff
| (@of_cat_hom _ _ X Y f) := of_cat_obj Y 
| (@colimit_cocone_comp _ _ 𝒟 _ F_obj F_hom X _ _) := by exactI colimit_obj F_obj @F_hom
| (@is_colimit _ _ 𝒟 _ F_obj F_hom cocone_obj cocone) := cocone_obj
| (@limit_cone_comp _ _ 𝒟 _ F_obj F_hom X Y f) := Y
| (@is_limit _ _ 𝒟 _ F_obj F_hom cone_obj cone) := by exactI limit_obj F_obj @F_hom


variable (𝒞)

def obj₁ : Type 1 := bicompletion_aux 𝒞 ff

variable {𝒞}
variables {𝒟 : Type} [category.{0} 𝒟]

def hom₁ (X Y : obj₁ 𝒞) : Type 1 :=
{ f : bicompletion_aux 𝒞 tt // f.dom = X ∧ f.cod = Y }

@[simp] lemma coe_dom {X Y : obj₁ 𝒞} (f : hom₁ X Y) :
  (@coe { f : bicompletion_aux 𝒞 tt // f.dom = X ∧ f.cod = Y } 
    (bicompletion_aux 𝒞 tt) _ f).dom = X := f.2.1

@[simp] lemma coe_cod {X Y : obj₁ 𝒞} (f : hom₁ X Y) :
  (@coe { f : bicompletion_aux 𝒞 tt // f.dom = X ∧ f.cod = Y } 
    (bicompletion_aux 𝒞 tt) _ f).cod = Y := f.2.2

def of_cat_obj₁ (X : 𝒞) : obj₁ 𝒞 := of_cat_obj X

def limit_obj₁ (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) : obj₁ 𝒞 :=
limit_obj F_obj (λ X Y f, (F_hom f).1)

def colimit_obj₁ (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) : obj₁ 𝒞 :=
colimit_obj F_obj (λ X Y f, (F_hom f).1)

def of_cat_hom₁ {X Y : 𝒞} (f : X ⟶ Y) : hom₁ (of_cat_obj X) (of_cat_obj Y) :=
⟨of_cat_hom f, by simp⟩

def limit_cone_comp₁ (F_obj : 𝒟 → obj₁ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) (X : 𝒟) 
  {Y : obj₁ 𝒞} (f : hom₁ (F_obj X) Y) :
  hom₁ (limit_obj₁ F_obj @F_hom) Y :=
⟨limit_cone_comp F_obj (λ X Y f, (F_hom f).1) X Y f.1, by simp [limit_obj₁]⟩

def colimit_cocone_comp₁ (F_obj : 𝒟 → obj₁ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) (X : 𝒟) 
  {Y : obj₁ 𝒞} (f : hom₁ Y (F_obj X)) :
  hom₁ Y (colimit_obj₁ F_obj @F_hom) :=
⟨colimit_cocone_comp F_obj (λ X Y f, (F_hom f).1) X Y f.1, by simp [colimit_obj₁]⟩

def is_limit₁ (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (cone_obj : obj₁ 𝒞)
  (cone : Π (X : 𝒟), hom₁ cone_obj (F_obj X)) :
  hom₁ cone_obj (limit_obj₁ F_obj @F_hom) :=
⟨is_limit F_obj (λ X Y f, (F_hom f).1) cone_obj (λ X, (cone X).1), by simp [limit_obj₁]⟩

def is_colimit₁ (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (cocone_obj : obj₁ 𝒞)
  (cocone : Π (X : 𝒟), hom₁ (F_obj X) cocone_obj) :
  hom₁ (colimit_obj₁ F_obj @F_hom) cocone_obj  :=
⟨is_colimit F_obj (λ X Y f, (F_hom f).1) cocone_obj (λ X, (cocone X).1), by simp [colimit_obj₁]⟩

def id₁_aux (b : bool) (hb : b = ff) (X : bicompletion_aux 𝒞 b) : 
  hom₁ (show bicompletion_aux 𝒞 ff, from eq.rec_on hb X)
       (show bicompletion_aux 𝒞 ff, from eq.rec_on hb X) :=
begin
  revert hb,
  refine bicompletion_aux.rec_on X _ _ _ _ _ _ _ _,
  { rintros X h,
    exact of_cat_hom₁ (𝟙 X) },
  { introsI 𝒟 _ F_obj F_hom ih₁ ih₂ _, 
    exact ⟨is_limit F_obj @F_hom (limit_obj F_obj @F_hom) 
      (λ D, limit_cone_comp F_obj @F_hom D (F_obj D) (ih₁ D rfl).1), 
      by simp⟩ },
  { introsI 𝒟 _ F_obj F_hom ih₁ ih₂ _, 
    exact ⟨is_colimit F_obj @F_hom (colimit_obj F_obj @F_hom) 
      (λ D, colimit_cocone_comp F_obj @F_hom D (F_obj D) (ih₁ D rfl).1),
      by simp⟩ },
  all_goals { intros, contradiction }
end

def id₁ (X : obj₁ 𝒞) : hom₁ X X :=
id₁_aux ff rfl X

inductive valid_obj₁ : Π (X : obj₁ 𝒞), Prop
| of_cat_obj (X : 𝒞) : valid_obj₁ (of_cat_obj X)
| limit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) 
  (h : Π X : 𝒟, valid_obj₁ (F_obj X)) : 
  valid_obj₁ (limit_obj₁ F_obj @F_hom)
| colimit_obj {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (h : Π X : 𝒟, valid_obj₁ (F_obj X)) :
  valid_obj₁ (colimit_obj₁ F_obj @F_hom)

def valid_obj₁_limit_obj 
  {𝒟 : Type} [category.{0} 𝒟] {F_obj : 𝒟 → obj₁ 𝒞}
  {F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt}
  (h : valid_obj₁ (limit_obj F_obj @F_hom)) :
  Π (X : 𝒟), valid_obj₁ (F_obj X) :=
begin
  generalize hX : limit_obj F_obj @F_hom = X,
  rw hX at h,
  induction h,
  { simp * at * },
  { simp [limit_obj₁] at hX,
    rcases hX with ⟨hX₁, hX₂, hX₂, hX₄⟩,
    subst hX₁,
    simp at *,
    subst hX₂,
    assumption },
  { simp [*, colimit_obj₁] at * }
end

def valid_obj₁_colimit_obj 
  {𝒟 : Type} [category.{0} 𝒟] {F_obj : 𝒟 → obj₁ 𝒞}
  {F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → bicompletion_aux 𝒞 tt}
  (h : valid_obj₁ (colimit_obj F_obj @F_hom)) :
  Π (X : 𝒟), valid_obj₁ (F_obj X) :=
begin
  generalize hX : colimit_obj F_obj @F_hom = X,
  rw hX at h,
  induction h,
  { simp * at * },
  { simp [*, limit_obj₁] at * },
  { simp [colimit_obj₁] at hX,
    rcases hX with ⟨hX₁, hX₂, hX₂, hX₄⟩,
    subst hX₁,
    simp at *,
    subst hX₂,
    assumption }
end

@[elab_as_eliminator] def hom_rec_on {motive : bicompletion_aux 𝒞 tt → Sort u}
  (f : bicompletion_aux 𝒞 tt)
  (of_cat_hom : Π {X Y : 𝒞} (f : X ⟶ Y), motive (of_cat_hom f))
  (limit_cone_comp : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → bicompletion_aux 𝒞 tt) (X : 𝒟) (Y : bicompletion_aux 𝒞 ff)
    (f : bicompletion_aux 𝒞 tt),
    (Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f)) →
    motive f → motive (by exactI limit_cone_comp F_obj @F_hom X Y f))
  (is_limit : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → bicompletion_aux 𝒞 tt) (cone_obj : bicompletion_aux 𝒞 ff)
    (cone : 𝒟 → bicompletion_aux 𝒞 tt),
    (Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f)) →
    (Π (X : 𝒟), motive (cone X)) → motive (by exactI is_limit F_obj @F_hom cone_obj cone))
  (colimit_cocone_comp : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → bicompletion_aux 𝒞 tt) (X : 𝒟) (Y : bicompletion_aux 𝒞 ff)
    (f : bicompletion_aux 𝒞 tt),
    (Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f)) →
    motive f → motive (by exactI colimit_cocone_comp F_obj @F_hom X Y f))
  (is_colimit : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → bicompletion_aux 𝒞 ff)
   (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → bicompletion_aux 𝒞 tt) (cocone_obj : bicompletion_aux 𝒞 ff)
   (cocone : 𝒟 → bicompletion_aux 𝒞 tt),
     (Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f)) →
     (Π (X : 𝒟), motive (cocone X)) → motive (by exactI is_colimit F_obj @F_hom cocone_obj cocone)) :
  motive f :=
have ∀ b (f : bicompletion_aux 𝒞 b) (h : b = tt), motive (eq.rec_on h f) :=
  begin
    intros b f,
    refine bicompletion_aux.rec_on f _ _ _ _ _ _ _ _,
    { intros, simp at *, contradiction },
    { intros, simp at *, contradiction },
    { intros, simp at *, contradiction },
    { intros X Y f _,
      exact of_cat_hom f },
    { introsI 𝒟 _ F_obj F_hom X Y f ih₁ ih₂ ih₃ ih₄ _,
      exact limit_cone_comp F_obj @F_hom X Y f (λ X Y f, ih₂ f rfl) (ih₄ rfl) },
    { introsI 𝒟 _ F_obj F_hom cone_obj cone ih₁ ih₂ ih₃ ih₄ _,
      exact is_limit F_obj @F_hom cone_obj cone (λ X Y f, ih₂ f rfl) (λ X, ih₄ X rfl) },
    { introsI 𝒟 _ F_obj F_hom X Y f ih₁ ih₂ ih₃ ih₄ _,
      exact colimit_cocone_comp F_obj @F_hom X Y f (λ X Y f, ih₂ f rfl) (ih₄ rfl) },
    { introsI 𝒟 _ F_obj F_hom cone_obj cone ih₁ ih₂ ih₃ ih₄ _,
      exact is_colimit F_obj @F_hom cone_obj cone (λ X Y f, ih₂ f rfl) (λ X, ih₄ X rfl) },
  end,
this tt f rfl

inductive valid_hom₁ : Π {X Y : obj₁ 𝒞}, hom₁ X Y → Prop
| of_cat_hom {X Y : 𝒞} (f : X ⟶ Y) : valid_hom₁ (of_cat_hom₁ f)
| id (X : obj₁ 𝒞) : valid_hom₁ (id₁ X)
| limit_cone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞)
  (obj_valid : ∀ X, valid_obj₁ (F_obj X))
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) 
  (X : 𝒟) {Y : obj₁ 𝒞} (f : hom₁ (F_obj X) Y) 
  (F_hom_valid : Π {X Y : 𝒟} (f : X ⟶ Y), valid_hom₁ (F_hom f))
  (f_valid : valid_hom₁ f) :
  valid_hom₁ (limit_cone_comp₁ F_obj @F_hom X f)
| colimit_cocone_comp {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞)
  (obj_valid : ∀ X, valid_obj₁ (F_obj X))
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y)) 
  (X : 𝒟) {Y : obj₁ 𝒞} (f : hom₁ Y (F_obj X)) 
  (F_hom_valid : Π {X Y : 𝒟} (f : X ⟶ Y), valid_hom₁ (F_hom f))
  (f_valid : valid_hom₁ f) :
  valid_hom₁ (colimit_cocone_comp₁ F_obj @F_hom X f)
| is_limit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞)
  (obj_valid : ∀ X, valid_obj₁ (F_obj X))
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (cone_obj : obj₁ 𝒞)
  (cone : Π (X : 𝒟), hom₁ cone_obj (F_obj X)) 
  (F_hom_valid : Π {X Y : 𝒟} (f : X ⟶ Y), valid_hom₁ (F_hom f))
  (cone_valid : Π (X : 𝒟), valid_hom₁ (cone X)) :
  valid_hom₁ (is_limit₁ F_obj @F_hom cone_obj cone)
| is_colimit {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₁ 𝒞)
  (obj_valid : ∀ X, valid_obj₁ (F_obj X))
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₁ (F_obj X) (F_obj Y))
  (cocone_obj : obj₁ 𝒞)
  (cocone : Π (X : 𝒟), hom₁ (F_obj X) cocone_obj) 
  (F_hom_valid : Π {X Y : 𝒟} (f : X ⟶ Y), valid_hom₁ (F_hom f))
  (cocone_valid : Π (X : 𝒟), valid_hom₁ (cocone X)) :
  valid_hom₁ (is_colimit₁ F_obj @F_hom cocone_obj cocone)

variable (𝒞)

def obj₂ : Type 1 := { X : obj₁ 𝒞 // valid_obj₁ X } 

variable {𝒞}

def hom₂ (X Y : obj₂ 𝒞) : Type 1 := { f : hom₁ X.1 Y.1 // valid_hom₁ f }

open valid_hom₁

def of_cat_obj₂ (X : 𝒞) : obj₂ 𝒞 :=
⟨of_cat_obj X, valid_obj₁.of_cat_obj _⟩ 

lemma of_cat_obj₂_injective : function.injective (@of_cat_obj₂ 𝒞 _) :=
begin
  intros X Y hXY,
  simp [of_cat_obj₂] at hXY,
  injection hXY,
end

def limit_obj₂ (F_obj : 𝒟 → obj₂ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) : obj₂ 𝒞 :=
⟨limit_obj₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1), valid_obj₁.limit_obj _ _ (λ X, (F_obj X).2)⟩

lemma limit_obj₂_injective {𝒟₁ 𝒟₂ : Type} [i₁ : category 𝒟₁] [i₂ : category 𝒟₂] 
  {F_obj₁ : 𝒟₁ → obj₂ 𝒞} {F_obj₂ : 𝒟₂ → obj₂ 𝒞} 
  {F_hom₁ : Π {X Y : 𝒟₁}, (X ⟶ Y) → hom₂ (F_obj₁ X) (F_obj₁ Y)}
  {F_hom₂ : Π {X Y : 𝒟₂}, (X ⟶ Y) → hom₂ (F_obj₂ X) (F_obj₂ Y)}
  (h : limit_obj₂ F_obj₁ @F_hom₁ = limit_obj₂ F_obj₂ @F_hom₂) : 
  𝒟₁ = 𝒟₂ ∧ i₁ == i₂ ∧ F_obj₁ == F_obj₂ ∧ @F_hom₁ == @F_hom₂ :=
begin
  simp [limit_obj₂, limit_obj₁] at h,
  injection h with h₁ h₂ h₃ h₄,
  unfreezingI { subst h₁ },
  rw heq_iff_eq at h₂,
  unfreezingI { subst h₂ },
  simp [heq_iff_eq, function.funext_iff, subtype.coe_injective.eq_iff] at h₃,
  rw [← function.funext_iff] at h₃,
  dsimp at h₃,
  subst h₃,
  simp [heq_iff_eq, function.funext_iff, subtype.coe_injective.eq_iff] at h₄,
  simp,
  ext,
  simp *
end

def colimit_obj₂ (F_obj : 𝒟 → obj₂ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) : obj₂ 𝒞 :=
⟨colimit_obj₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1), valid_obj₁.colimit_obj _ _ (λ X, (F_obj X).2)⟩

lemma colimit_obj₂_injective {𝒟₁ 𝒟₂ : Type} [i₁ : category 𝒟₁] [i₂ : category 𝒟₂] 
  {F_obj₁ : 𝒟₁ → obj₂ 𝒞} {F_obj₂ : 𝒟₂ → obj₂ 𝒞} 
  {F_hom₁ : Π {X Y : 𝒟₁}, (X ⟶ Y) → hom₂ (F_obj₁ X) (F_obj₁ Y)}
  {F_hom₂ : Π {X Y : 𝒟₂}, (X ⟶ Y) → hom₂ (F_obj₂ X) (F_obj₂ Y)}
  (h : colimit_obj₂ F_obj₁ @F_hom₁ = colimit_obj₂ F_obj₂ @F_hom₂) : 
  𝒟₁ = 𝒟₂ ∧ i₁ == i₂ ∧ F_obj₁ == F_obj₂ ∧ @F_hom₁ == @F_hom₂ :=
begin
  simp [colimit_obj₂, colimit_obj₁] at h,
  injection h with h₁ h₂ h₃ h₄,
  unfreezingI { subst h₁ },
  rw heq_iff_eq at h₂,
  unfreezingI { subst h₂ },
  simp [heq_iff_eq, function.funext_iff, subtype.coe_injective.eq_iff] at h₃,
  rw [← function.funext_iff] at h₃,
  dsimp at h₃,
  subst h₃,
  simp [heq_iff_eq, function.funext_iff, subtype.coe_injective.eq_iff] at h₄,
  simp,
  ext,
  simp *
end

def of_cat_hom₂ {X Y : 𝒞} (f : X ⟶ Y) : hom₂ (of_cat_obj₂ X) (of_cat_obj₂ Y) :=
⟨of_cat_hom₁ f, valid_hom₁.of_cat_hom _⟩ 

def limit_cone_comp₂ (F_obj : 𝒟 → obj₂ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) (X : 𝒟) 
  {Y : obj₂ 𝒞} (f : hom₂ (F_obj X) Y) :
  hom₂ (limit_obj₂ F_obj @F_hom) Y :=
⟨limit_cone_comp₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1) X f.1, 
  valid_hom₁.limit_cone_comp _ (λ X, (F_obj X).2) _ _ _ (λ X Y f, (F_hom f).2) f.2⟩

def colimit_cocone_comp₂ (F_obj : 𝒟 → obj₂ 𝒞)
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) (X : 𝒟) 
  {Y : obj₂ 𝒞} (f : hom₂ Y (F_obj X)):
  hom₂ Y (colimit_obj₂ F_obj @F_hom) :=
⟨colimit_cocone_comp₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1) X f.1, 
  valid_hom₁.colimit_cocone_comp _ (λ X, (F_obj X).2) _ _ _ (λ X Y f, (F_hom f).2) f.2⟩

def is_limit₂ (F_obj : 𝒟 → obj₂ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
  (cone_obj : obj₂ 𝒞)
  (cone : Π (X : 𝒟), hom₂ cone_obj (F_obj X)) :
  hom₂ cone_obj (limit_obj₂ F_obj @F_hom) :=
⟨is_limit₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1) cone_obj.1 (λ X, (cone X).1), 
  valid_hom₁.is_limit _ (λ X, (F_obj X).2) _ _ _ (λ X Y f, (F_hom f).2) (λ X, (cone X).2)⟩

def is_colimit₂ (F_obj : 𝒟 → obj₂ 𝒞) 
  (F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
  (cocone_obj : obj₂ 𝒞)
  (cocone : Π (X : 𝒟), hom₂ (F_obj X) cocone_obj) :
  hom₂ (colimit_obj₂ F_obj @F_hom) cocone_obj  :=
⟨is_colimit₁ (λ X, (F_obj X).1) (λ X Y f, (F_hom f).1) cocone_obj.1 (λ X, (cocone X).1), 
  valid_hom₁.is_colimit _ (λ X, (F_obj X).2) _ _ _ (λ X Y f, (F_hom f).2) (λ X, (cocone X).2)⟩

-- @[elab_as_eliminator] def rec₂_aux
--   {obj_motive : obj₂ 𝒞 → Sort u} 
--   {hom_motive : Π {X Y : obj₂ 𝒞}, obj_motive X → obj_motive Y → hom₂ X Y → Sort v}
--   (of_cat_obj : Π (X : 𝒞), obj_motive (of_cat_obj₂ X))
--   (limit_obj : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f)), 
--     by exactI obj_motive (limit_obj₂ F_obj @F_hom))
--   (colimit_obj : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f)), 
--     by exactI obj_motive (colimit_obj₂ F_obj @F_hom))
--   (of_cat_hom : Π {X Y : 𝒞} (f : X ⟶ Y), 
--     hom_motive (of_cat_obj X) (of_cat_obj Y) (of_cat_hom₂ f))
--   (limit_cone_comp : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f))
--     (X : 𝒟) {Y : obj₂ 𝒞} (ih_Y : obj_motive Y) (f : hom₂ (F_obj X) Y)
--     (ih_f : hom_motive (ih_F_obj X) ih_Y f),
--       by exactI hom_motive (limit_obj F_obj ih_F_obj @F_hom @ih_F_hom) ih_Y 
--         (by exactI limit_cone_comp₂ F_obj @F_hom X f))
--   (colimit_cocone_comp : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f))
--     (X : 𝒟) {Y : obj₂ 𝒞} (ih_Y : obj_motive Y) (f : hom₂ Y (F_obj X))
--     (ih_f : hom_motive ih_Y (ih_F_obj X) f),
--       by exactI hom_motive ih_Y (colimit_obj F_obj ih_F_obj @F_hom @ih_F_hom)
--         (by exactI colimit_cocone_comp₂ F_obj @F_hom X f))
--   (is_limit : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f)) 
--     (cone_obj : obj₂ 𝒞) (ih_cone_obj : obj_motive cone_obj) 
--     (cone : Π (X : 𝒟), hom₂ cone_obj (F_obj X))
--     (ih_cone : Π (X : 𝒟), hom_motive ih_cone_obj (ih_F_obj X) (cone X)),
--       by exactI hom_motive ih_cone_obj (limit_obj F_obj ih_F_obj @F_hom @ih_F_hom) 
--         (by exactI is_limit₂ F_obj @F_hom cone_obj cone))
--   (is_colimit : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f)) 
--     (cocone_obj : obj₂ 𝒞) (ih_cocone_obj : obj_motive cocone_obj) 
--     (cocone : Π (X : 𝒟), hom₂ (F_obj X) cocone_obj)
--     (ih_cocone : Π (X : 𝒟), hom_motive (ih_F_obj X) ih_cocone_obj (cocone X)),
--       by exactI hom_motive (colimit_obj F_obj ih_F_obj @F_hom @ih_F_hom) ih_cocone_obj
--         (is_colimit₂ F_obj @F_hom cocone_obj cocone)) 
--   (b : bool) (f : bicompletion_aux 𝒞 b) :
--   pprod (∀ (h : b = ff), let f' : bicompletion_aux 𝒞 ff := eq.rec_on h f in
--     ∀ (hv : valid_obj₁ f'), obj_motive ⟨f', hv⟩)
--   (∀ h : b = tt, let f' : bicompletion_aux 𝒞 tt := eq.rec_on h f in 
--     ∀ (hv : valid_hom₁ ⟨f', rfl, rfl⟩)
--     (hv₁ : valid_obj₁ f'.dom)
--     (hv₂ : valid_obj₁ f'.cod)
--     (h₁ : obj_motive ⟨f'.dom, hv₁⟩)
--     (h₂ : obj_motive ⟨f'.cod, hv₂⟩), 
--     hom_motive h₁ h₂ ⟨⟨f', rfl, rfl⟩, hv⟩) :=
-- begin
--   refine bicompletion_aux.rec_on f _ _ _ _ _ _ _ _,
--   { intros X,
--     exact ⟨λ _ hX, of_cat_obj X, λ _, by contradiction⟩ },
--   { introsI 𝒟 _ F_obj F_hom ih₁ ih₂,
--     refine ⟨λ _ hv, _, λ _, by contradiction⟩,
--     dsimp at *,
--     have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
--     { cases hv, assumption },
--     let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
--     have valid_F_hom : ∀ X Y f, 
--       ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
--       (h₂ : (@F_hom X Y f).cod = F_obj Y),
--       valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
--     { cases hv, simp,  },
--     let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
--       λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
--         (valid_F_hom X Y f).snd.snd⟩,
--     have := limit_obj F_obj' F_hom' _ _
--      },
--   { intros A B f X Y hX hY hfd hfc hf,
--     dsimp at hfd hfc, substs hfc hfd,
--     exact of_cat_hom f },
--   { introsI 𝒟 _ F_obj F_hom A B g ih₁ ih₂ X Y hX hY hfd hfc hf,
--     dsimp at hfd hfc, substs hfc hfd,
--     have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
--     { cases hf, assumption },
--     let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
--     have valid_F_hom : ∀ X Y f, 
--       ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
--       (h₂ : (@F_hom X Y f).cod = F_obj Y),
--       valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
--     { cases hf, simpa },
--      let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
--       λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
--         (valid_F_hom X Y f).snd.snd⟩,
--     have valid_g : 
--       ∃ (h₁ : g.dom = F_obj A) (h₂ : g.cod = B),
--       valid_hom₁ ⟨g, h₁, h₂⟩,
--     { cases hf, simpa },
--     let g' : hom₂ (F_obj' A) ⟨B, hY⟩ :=
--       ⟨⟨g, valid_g.fst, valid_g.snd.fst⟩, valid_g.snd.snd⟩,
--     exact limit_cone_comp F_obj' F_hom'
--       (λ X Y f, ih₁ f (F_obj X) (F_obj Y) (valid_F_obj _) (valid_F_obj _)
--           (valid_F_hom _ _ f).fst (valid_F_hom _ _ f).snd.fst
--           (valid_F_hom _ _ f).snd.snd) A g'
--           (ih₂ (F_obj' A).1 B (F_obj' A).2 hY g'.1.2.1 g'.1.2.2 g'.2) },
--     { introsI 𝒟 _ F_obj F_hom cone_obj cone ih₁ ih₂ X Y hX hY hfd hfc hf,
--       dsimp at hfd hfc,
--       substs hfc hfd,
--       have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
--       { cases hf, assumption },
--       let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
--       have valid_F_hom : ∀ X Y f, 
--         ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
--         (h₂ : (@F_hom X Y f).cod = F_obj Y),
--         valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
--       { cases hf, simpa },
--       let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
--         λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
--           (valid_F_hom X Y f).snd.snd⟩,
--       let cone_obj' : obj₂ 𝒞 := ⟨cone_obj, hX⟩,
--       have valid_cone : ∀ (X : 𝒟), ∃ (h₁ : (cone X).dom = cone_obj'.1)
--         (h₂ : (cone X).cod = (F_obj' X).1),
--         valid_hom₁ ⟨cone X, h₁, h₂⟩,
--       { cases hf, simpa },
--       let cone' : Π (X : 𝒟), hom₂ cone_obj' (F_obj' X) :=
--         λ X, ⟨⟨cone X, (valid_cone X).fst, (valid_cone X).snd.fst⟩, (valid_cone X).snd.snd⟩,
--       exact is_limit F_obj' F_hom'
--         (λ A B f, ih₁ f (F_obj A) (F_obj B) (F_obj' A).2 (F_obj' B).2
--           (valid_F_hom _ _ f).fst (valid_F_hom _ _ f).snd.fst
--           (valid_F_hom _ _ f).snd.snd)
--           cone_obj' cone'
--           (λ X, ih₂ X cone_obj'.1 (F_obj' X).1 cone_obj'.2 (F_obj' X).2
--               (cone' X).1.2.1 (cone' X).1.2.2 (cone' X).2) },
--     { introsI 𝒟 _ F_obj F_hom A B g ih₁ ih₂ X Y hX hY hfd hfc hf,
--       dsimp at hfd hfc, substs hfc hfd,
--       have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
--       { cases hf, assumption },
--       let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
--       have valid_F_hom : ∀ X Y f, 
--         ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
--         (h₂ : (@F_hom X Y f).cod = F_obj Y),
--         valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
--       { cases hf, simpa },
--       have valid_g : 
--         ∃ (h₁ : g.dom = B) (h₂ : g.cod = F_obj A),
--         valid_hom₁ ⟨g, h₁, h₂⟩,
--       { cases hf, simpa },
--       let g' : hom₂ ⟨B, hX⟩ (F_obj' A) :=
--         ⟨⟨g, valid_g.fst, valid_g.snd.fst⟩, valid_g.snd.snd⟩,
--       let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
--         λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
--           (valid_F_hom X Y f).snd.snd⟩,
--       exact colimit_cocone_comp F_obj' F_hom'
--         (λ X Y f, ih₁ f (F_obj X) (F_obj Y) (valid_F_obj _) (valid_F_obj _)
--             (valid_F_hom _ _ f).fst (valid_F_hom _ _ f).snd.fst
--             (valid_F_hom _ _ f).snd.snd) A g'
--             (ih₂ B (F_obj' A).1 hX (F_obj' A).2 g'.1.2.1 g'.1.2.2 g'.2) },
--     { introsI 𝒟 _ F_obj F_hom cocone_obj cocone ih₁ ih₂ X Y hX hY hfd hfc hf,
--       dsimp at hfd hfc,
--       substs hfc hfd,
--       have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
--       { cases hf, assumption },
--       let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
--       have valid_F_hom : ∀ X Y f, 
--         ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
--         (h₂ : (@F_hom X Y f).cod = F_obj Y),
--         valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
--       { cases hf, simpa },
--       let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
--         λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
--           (valid_F_hom X Y f).snd.snd⟩,
--       let cocone_obj' : obj₂ 𝒞 := ⟨cocone_obj, hY⟩,
--       have valid_cocone : ∀ (X : 𝒟), ∃ (h₁ : (cocone X).dom = (F_obj' X).1)
--         (h₂ : (cocone X).cod = cocone_obj'.1),
--         valid_hom₁ ⟨cocone X, h₁, h₂⟩,
--       { cases hf, simpa },
--       let cocone' : Π (X : 𝒟), hom₂ (F_obj' X) cocone_obj' :=
--         λ X, ⟨⟨cocone X, (valid_cocone X).fst, (valid_cocone X).snd.fst⟩, (valid_cocone X).snd.snd⟩,
--       exact is_colimit F_obj' F_hom'
--         (λ A B f, ih₁ f (F_obj A) (F_obj B) (F_obj' A).2 (F_obj' B).2
--           (valid_F_hom _ _ f).fst (valid_F_hom _ _ f).snd.fst
--           (valid_F_hom _ _ f).snd.snd)
--           cocone_obj' cocone'
--           (λ X, ih₂ X (F_obj' X).1 cocone_obj'.1 (F_obj' X).2 cocone_obj'.2 
--               (cocone' X).1.2.1 (cocone' X).1.2.2 (cocone' X).2) }
-- end

-- @[elab_as_eliminator] protected def rec_on₂
--   {obj_motive : obj₂ 𝒞 → Sort u} 
--   {hom_motive : Π {X Y : obj₂ 𝒞}, obj_motive X → obj_motive Y → hom₂ X Y → Sort v}
--   (of_cat_obj : Π (X : 𝒞), obj_motive (of_cat_obj₂ X))
--   (limit_obj : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f)), 
--     by exactI obj_motive (limit_obj₂ F_obj @F_hom))
--   (colimit_obj : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f)), 
--     by exactI obj_motive (colimit_obj₂ F_obj @F_hom))
--   (of_cat_hom : Π {X Y : 𝒞} (f : X ⟶ Y), 
--     hom_motive (of_cat_obj X) (of_cat_obj Y) (of_cat_hom₂ f))
--   (limit_cone_comp : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f))
--     (X : 𝒟) {Y : obj₂ 𝒞} (ih_Y : obj_motive Y) (f : hom₂ (F_obj X) Y)
--     (ih_f : hom_motive (ih_F_obj X) ih_Y f),
--       by exactI hom_motive (limit_obj F_obj ih_F_obj @F_hom @ih_F_hom) ih_Y 
--         (by exactI limit_cone_comp₂ F_obj @F_hom X f))
--   (colimit_cocone_comp : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f))
--     (X : 𝒟) {Y : obj₂ 𝒞} (ih_Y : obj_motive Y) (f : hom₂ Y (F_obj X))
--     (ih_f : hom_motive ih_Y (ih_F_obj X) f),
--       by exactI hom_motive ih_Y (colimit_obj F_obj ih_F_obj @F_hom @ih_F_hom)
--         (by exactI colimit_cocone_comp₂ F_obj @F_hom X f))
--   (is_limit : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f)) 
--     (cone_obj : obj₂ 𝒞) (ih_cone_obj : obj_motive cone_obj) 
--     (cone : Π (X : 𝒟), hom₂ cone_obj (F_obj X))
--     (ih_cone : Π (X : 𝒟), hom_motive ih_cone_obj (ih_F_obj X) (cone X)),
--       by exactI hom_motive ih_cone_obj (limit_obj F_obj ih_F_obj @F_hom @ih_F_hom) 
--         (by exactI is_limit₂ F_obj @F_hom cone_obj cone))
--   (is_colimit : Π {𝒟 : Type} [category.{0} 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
--     (ih_F_obj : Π (X : 𝒟), obj_motive (F_obj X))
--     (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
--     (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), 
--       hom_motive (ih_F_obj X) (ih_F_obj Y) (F_hom f)) 
--     (cocone_obj : obj₂ 𝒞) (ih_cocone_obj : obj_motive cocone_obj) 
--     (cocone : Π (X : 𝒟), hom₂ (F_obj X) cocone_obj)
--     (ih_cocone : Π (X : 𝒟), hom_motive (ih_F_obj X) ih_cocone_obj (cocone X)),
--       by exactI hom_motive (colimit_obj F_obj ih_F_obj @F_hom @ih_F_hom) ih_cocone_obj
--         (is_colimit₂ F_obj @F_hom cocone_obj cocone)) :
--   Σ' (obj_h : Π (X : obj₂ 𝒞), obj_motive X), Π (X Y : obj₂ 𝒞) (f : hom₂ X Y), 
--     hom_motive (obj_h X) (obj_h Y) f :=
-- begin
--   have := @rec₂_aux 𝒞 _ @obj_motive @hom_motive
--       @of_cat_obj @limit_obj @colimit_obj
--       @of_cat_hom @limit_cone_comp @colimit_cocone_comp
--       @is_limit @is_colimit,
--    have obj_h : ∀ X, obj_motive X,
--   { intro X,
--     cases X with X hX, exact (this ff X).1 rfl hX },
--   split,
--   swap,
--   { exact obj_h },
--   { intros X Y f,
--     cases X with X hX,
--     cases Y with Y hY,
--     rcases f with ⟨⟨f, hf₁, hf₂⟩, hf⟩,
--     dsimp at hf₁ hf₂, substs hf₁ hf₂,
--     exact (this tt f).2 rfl hf hX hY (obj_h _) (obj_h _) }
-- end

@[elab_as_eliminator] protected def hom₂.rec_on 
  {motive : Π {X Y : obj₂ 𝒞} (f : hom₂ X Y), Sort*} {X Y : obj₂ 𝒞} (f : hom₂ X Y)
  (of_cat_hom : Π {X Y : 𝒞} (f : X ⟶ Y), motive (of_cat_hom₂ f))
  (limit_cone_comp : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f))
    (X : 𝒟) {Y : obj₂ 𝒞} (f : hom₂ (F_obj X) Y)
    (ih_f : motive f),
      motive (by exactI limit_cone_comp₂ F_obj @F_hom X f))
  (colimit_cocone_comp : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) 
    (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f))
    (X : 𝒟) {Y : obj₂ 𝒞} (f : hom₂ Y (F_obj X))
    (ih_f : motive f),
      motive (by exactI colimit_cocone_comp₂ F_obj @F_hom X f))
  (is_limit : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f)) 
    (cone_obj : obj₂ 𝒞) (cone : Π (X : 𝒟), hom₂ cone_obj (F_obj X))
    (ih_cone : Π (X : 𝒟), motive (cone X)),
      motive (by exactI is_limit₂ F_obj @F_hom cone_obj cone))
  (is_colimit : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) 
    (ih_F_hom : Π {X Y : 𝒟} (f : by exactI X ⟶ Y), motive (F_hom f))
    (cocone_obj : obj₂ 𝒞) (cocone : Π (X : 𝒟), hom₂ (F_obj X) cocone_obj)
    (ih_cone : Π (X : 𝒟), motive (cocone X)),
      motive (by exactI is_colimit₂ F_obj @F_hom cocone_obj cocone)) :
  motive f :=
begin
  cases X with X hX, cases Y with Y hY,
  cases f with f hf,
  rcases f with ⟨f, hfd, hfc⟩,
  revert X Y hX hY,
  refine hom_rec_on f _ _ _ _ _,
  { intros A B f X Y hX hY hfd hfc hf,
    dsimp at hfd hfc, substs hfc hfd,
    exact of_cat_hom f },
  { introsI 𝒟 _ F_obj F_hom A B g ih₁ ih₂ X Y hX hY hfd hfc hf,
    dsimp at hfd hfc, substs hfc hfd,
    have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
    { cases hf, assumption },
    let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
    have valid_F_hom : ∀ X Y f, 
      ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
      (h₂ : (@F_hom X Y f).cod = F_obj Y),
      valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
    { cases hf, simpa },
     let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
      λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
        (valid_F_hom X Y f).snd.snd⟩,
    have valid_g : 
      ∃ (h₁ : g.dom = F_obj A) (h₂ : g.cod = B),
      valid_hom₁ ⟨g, h₁, h₂⟩,
    { cases hf, simpa },
    let g' : hom₂ (F_obj' A) ⟨B, hY⟩ :=
      ⟨⟨g, valid_g.fst, valid_g.snd.fst⟩, valid_g.snd.snd⟩,
    exact limit_cone_comp F_obj' F_hom'
      (λ X Y f, ih₁ f (F_obj X) (F_obj Y) (valid_F_obj _) (valid_F_obj _)
          (valid_F_hom _ _ f).fst (valid_F_hom _ _ f).snd.fst
          (valid_F_hom _ _ f).snd.snd) A g'
          (ih₂ (F_obj' A).1 B (F_obj' A).2 hY g'.1.2.1 g'.1.2.2 g'.2) },
    { introsI 𝒟 _ F_obj F_hom cone_obj cone ih₁ ih₂ X Y hX hY hfd hfc hf,
      dsimp at hfd hfc,
      substs hfc hfd,
      have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
      { cases hf, assumption },
      let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
      have valid_F_hom : ∀ X Y f, 
        ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
        (h₂ : (@F_hom X Y f).cod = F_obj Y),
        valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
      { cases hf, simpa },
      let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
        λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
          (valid_F_hom X Y f).snd.snd⟩,
      let cone_obj' : obj₂ 𝒞 := ⟨cone_obj, hX⟩,
      have valid_cone : ∀ (X : 𝒟), ∃ (h₁ : (cone X).dom = cone_obj'.1)
        (h₂ : (cone X).cod = (F_obj' X).1),
        valid_hom₁ ⟨cone X, h₁, h₂⟩,
      { cases hf, simpa },
      let cone' : Π (X : 𝒟), hom₂ cone_obj' (F_obj' X) :=
        λ X, ⟨⟨cone X, (valid_cone X).fst, (valid_cone X).snd.fst⟩, (valid_cone X).snd.snd⟩,
      exact is_limit F_obj' F_hom'
        (λ A B f, ih₁ f (F_obj A) (F_obj B) (F_obj' A).2 (F_obj' B).2
          (valid_F_hom _ _ f).fst (valid_F_hom _ _ f).snd.fst
          (valid_F_hom _ _ f).snd.snd)
          cone_obj' cone'
          (λ X, ih₂ X cone_obj'.1 (F_obj' X).1 cone_obj'.2 (F_obj' X).2
              (cone' X).1.2.1 (cone' X).1.2.2 (cone' X).2) },
    { introsI 𝒟 _ F_obj F_hom A B g ih₁ ih₂ X Y hX hY hfd hfc hf,
      dsimp at hfd hfc, substs hfc hfd,
      have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
      { cases hf, assumption },
      let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
      have valid_F_hom : ∀ X Y f, 
        ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
        (h₂ : (@F_hom X Y f).cod = F_obj Y),
        valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
      { cases hf, simpa },
      have valid_g : 
        ∃ (h₁ : g.dom = B) (h₂ : g.cod = F_obj A),
        valid_hom₁ ⟨g, h₁, h₂⟩,
      { cases hf, simpa },
      let g' : hom₂ ⟨B, hX⟩ (F_obj' A) :=
        ⟨⟨g, valid_g.fst, valid_g.snd.fst⟩, valid_g.snd.snd⟩,
      let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
        λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
          (valid_F_hom X Y f).snd.snd⟩,
      exact colimit_cocone_comp F_obj' F_hom'
        (λ X Y f, ih₁ f (F_obj X) (F_obj Y) (valid_F_obj _) (valid_F_obj _)
            (valid_F_hom _ _ f).fst (valid_F_hom _ _ f).snd.fst
            (valid_F_hom _ _ f).snd.snd) A g'
            (ih₂ B (F_obj' A).1 hX (F_obj' A).2 g'.1.2.1 g'.1.2.2 g'.2) },
    { introsI 𝒟 _ F_obj F_hom cocone_obj cocone ih₁ ih₂ X Y hX hY hfd hfc hf,
      dsimp at hfd hfc,
      substs hfc hfd,
      have valid_F_obj : ∀ X, valid_obj₁ (F_obj X),
      { cases hf, assumption },
      let F_obj' : 𝒟 → obj₂ 𝒞 := λ X, ⟨F_obj X, valid_F_obj X⟩,
      have valid_F_hom : ∀ X Y f, 
        ∃ (h₁ : (@F_hom X Y f).dom = F_obj X) 
        (h₂ : (@F_hom X Y f).cod = F_obj Y),
        valid_hom₁ ⟨@F_hom X Y f, h₁, h₂⟩,
      { cases hf, simpa },
      let F_hom' : Π (X Y : 𝒟) (f : X ⟶ Y), hom₂ (F_obj' X) (F_obj' Y) :=
        λ X Y f, ⟨⟨@F_hom X Y f, (valid_F_hom X Y f).fst, (valid_F_hom X Y f).snd.fst⟩,
          (valid_F_hom X Y f).snd.snd⟩,
      let cocone_obj' : obj₂ 𝒞 := ⟨cocone_obj, hY⟩,
      have valid_cocone : ∀ (X : 𝒟), ∃ (h₁ : (cocone X).dom = (F_obj' X).1)
        (h₂ : (cocone X).cod = cocone_obj'.1),
        valid_hom₁ ⟨cocone X, h₁, h₂⟩,
      { cases hf, simpa },
      let cocone' : Π (X : 𝒟), hom₂ (F_obj' X) cocone_obj' :=
        λ X, ⟨⟨cocone X, (valid_cocone X).fst, (valid_cocone X).snd.fst⟩, (valid_cocone X).snd.snd⟩,
      exact is_colimit F_obj' F_hom'
        (λ A B f, ih₁ f (F_obj A) (F_obj B) (F_obj' A).2 (F_obj' B).2
          (valid_F_hom _ _ f).fst (valid_F_hom _ _ f).snd.fst
          (valid_F_hom _ _ f).snd.snd)
          cocone_obj' cocone'
          (λ X, ih₂ X (F_obj' X).1 cocone_obj'.1 (F_obj' X).2 cocone_obj'.2 
              (cocone' X).1.2.1 (cocone' X).1.2.2 (cocone' X).2) }
end

def hom₂_of_cat_obj_rec_on
  {motive : Π {X : 𝒞} {Y : obj₂ 𝒞} (f : hom₂ (of_cat_obj₂ X) Y), Sort*} 
  {X : 𝒞} {Y : obj₂ 𝒞} (f : hom₂ (of_cat_obj₂ X) Y)
  (of_cat_hom : Π {Y : 𝒞} (f : X ⟶ Y), motive (of_cat_hom₂ f))
  (colimit_cocone_comp : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) 
    (X : 𝒟) {Y : 𝒞} (f : hom₂ (of_cat_obj₂ Y) (F_obj X))
    (ih_f : motive f),
      motive (by exactI colimit_cocone_comp₂ F_obj @F_hom X f))
  (is_limit : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    (cone_obj : 𝒞) (cone : Π (X : 𝒟), hom₂ (of_cat_obj₂ cone_obj) (F_obj X))
    (ih_cone : Π (X : 𝒟), motive (cone X)),
      motive (by exactI is_limit₂ F_obj @F_hom (of_cat_obj₂ cone_obj) cone)) :
  motive f := 
@hom₂.rec_on 𝒞 _ (λ A B f, ∀ (h : A = of_cat_obj₂ X),
  motive (show hom₂ (of_cat_obj₂ X) B, from eq.rec_on h f))
  (of_cat_obj₂ X) Y f 
  (λ A B g h, begin
      have := of_cat_obj₂_injective h,
      subst this,
      dsimp,
      exact of_cat_hom g
    end) 
  begin 
    intros,
    simp [limit_obj₂, of_cat_obj₂, limit_obj₁] at h,
    contradiction
  end 
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ A B g ih₂ h,
    subst h,
    exact colimit_cocone_comp _ _ _ _ (ih₂ rfl)
  end 
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ cone_obj cone ih₂ h,
    subst h,
    exact is_limit _ _ _ _ (λ A, ih₂ A rfl),
  end 
  begin 
    intros,
    simp [colimit_obj₂, of_cat_obj₂] at h,
    contradiction
  end  
  rfl

def hom₂_limit_obj_rec_on
  {motive : Π {𝒟 : Type} [category 𝒟] {F_obj : 𝒟 → obj₂ 𝒞}
    {F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)} {Y : obj₂ 𝒞}, 
    hom₂ (by exactI limit_obj₂ F_obj @F_hom) Y → Sort*}
  {𝒟 : Type} [category 𝒟] {F_obj : 𝒟 → obj₂ 𝒞}
  {F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)} {Y : obj₂ 𝒞}
  (f : hom₂ (limit_obj₂ F_obj @F_hom) Y)
  (limit_cone_comp : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    (X : 𝒟) {Y : obj₂ 𝒞} (f : hom₂ (F_obj X) Y),
      by exactI motive (limit_cone_comp₂ F_obj @F_hom X f))
  (colimit_cocone_comp : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    (X : 𝒟)
    {ℰ : Type} [category ℰ] (G_obj : ℰ → obj₂ 𝒞)
    (G_hom : Π {X Y : ℰ}, (by exactI X ⟶ Y) → hom₂ (G_obj X) (G_obj Y))
    (f : hom₂ (by exactI limit_obj₂ G_obj @G_hom) (F_obj X))
    (ih_f : by exactI motive f),
      by exactI motive (colimit_cocone_comp₂ F_obj @F_hom X f))
  (is_limit : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    {ℰ : Type} [category ℰ] (G_obj : ℰ → obj₂ 𝒞)
    (G_hom : Π {X Y : ℰ}, (by exactI X ⟶ Y) → hom₂ (G_obj X) (G_obj Y))
    (cone : Π (X : 𝒟), hom₂ (by exactI limit_obj₂ G_obj @G_hom) (F_obj X))
    (ih_cone : Π (X : 𝒟), by exactI motive (cone X)),
      by exactI motive (is_limit₂ F_obj @F_hom (limit_obj₂ G_obj @G_hom) cone)) :
  motive f :=
@hom₂.rec_on 𝒞 _ (λ A B f, ∀ (h : A = limit_obj₂ F_obj @F_hom),
  motive (show hom₂ (limit_obj₂ F_obj @F_hom) B, from eq.rec_on h f))
  (limit_obj₂ F_obj @F_hom) Y f 
  begin 
    intros,
    simp [limit_obj₂, of_cat_obj₂, limit_obj₁] at h,
    contradiction
  end  
  begin 
    introsI ℰ _ G_obj G_hom ih₁ A B g ih₂ h,
    unfreezingI { rcases (limit_obj₂_injective h) with ⟨rfl, h₁, h₂, h₃⟩ },
    unfreezingI { subst h₁, subst h₂, subst h₃ },
    exact limit_cone_comp _ _ _ _
  end 
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ A B g ih₂ h,
    subst h,
    exact colimit_cocone_comp _ _ _ _ _ _ (ih₂ rfl)
  end 
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ cone_obj cone ih₂ h,
    subst h,
    exact is_limit _ _ _ _ _ (λ A, ih₂ A rfl),
  end 
  begin 
    intros,
    simp [colimit_obj₂, of_cat_obj₂, limit_obj₂] at h,
    contradiction
  end  
  rfl

@[elab_as_eliminator] def hom₂_colimit_obj_rec_on
  {motive : Π {𝒟 : Type} [category 𝒟] {F_obj : 𝒟 → obj₂ 𝒞}
    {F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)} {Y : obj₂ 𝒞}, 
    hom₂ (by exactI colimit_obj₂ F_obj @F_hom) Y → Sort*}
  {𝒟 : Type} [category 𝒟] {F_obj : 𝒟 → obj₂ 𝒞}
  {F_hom : Π {X Y : 𝒟}, (X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)} {Y : obj₂ 𝒞}
  (f : hom₂ (colimit_obj₂ F_obj @F_hom) Y)
  (colimit_cocone_comp : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    (X : 𝒟) 
    {ℰ : Type} [category ℰ] {G_obj : ℰ → obj₂ 𝒞}
    {G_hom : Π {X Y : ℰ}, (by exactI X ⟶ Y) → hom₂ (G_obj X) (G_obj Y)} 
    (f : hom₂ (by exactI colimit_obj₂ G_obj @G_hom) (F_obj X))
    (ih_f : by exactI motive f),
      by exactI motive (by exactI colimit_cocone_comp₂ F_obj @F_hom X f))
  (is_limit : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y))
    {ℰ : Type} [category ℰ] {G_obj : ℰ → obj₂ 𝒞}
    {G_hom : Π {X Y : ℰ}, (by exactI X ⟶ Y) → hom₂ (G_obj X) (G_obj Y)}
    (cone : Π (X : 𝒟), hom₂ (by exactI colimit_obj₂ G_obj @G_hom) (F_obj X))
    (ih_cone : Π (X : 𝒟), by exactI motive (cone X)),
      by exactI motive (by exactI is_limit₂ F_obj @F_hom _ cone))
  (is_colimit : Π {𝒟 : Type} [category 𝒟] (F_obj : 𝒟 → obj₂ 𝒞)
    (F_hom : Π {X Y : 𝒟}, (by exactI X ⟶ Y) → hom₂ (F_obj X) (F_obj Y)) 
    (cocone_obj : obj₂ 𝒞) (cocone : Π (X : 𝒟), hom₂ (F_obj X) cocone_obj),
      by exactI motive (is_colimit₂ F_obj @F_hom cocone_obj cocone)) :
  motive f :=
@hom₂.rec_on 𝒞 _ (λ A B f, ∀ (h : A = colimit_obj₂ F_obj @F_hom),
  motive (show hom₂ (colimit_obj₂ F_obj @F_hom) B, from eq.rec_on h f))
  (colimit_obj₂ F_obj @F_hom) Y f 
  begin 
    intros,
    simp [colimit_obj₂, of_cat_obj₂, colimit_obj₁] at h,
    contradiction
  end 
  begin 
    intros,
    simp [colimit_obj₂, of_cat_obj₂, colimit_obj₁, limit_obj₁, limit_obj₂] at h,
    contradiction
  end
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ A B f ih₂ h,
    subst h,
    exact colimit_cocone_comp _ _ _ _ (ih₂ rfl)
  end
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ cone_obj cone ih₂ h,
    subst h,
    exact is_limit _ _ _ (λ X, ih₂ X rfl)
  end
  begin
    introsI ℰ _ G_obj G_hom ih₁ cocone_obj cocone ih₂ h,
    unfreezingI { rcases (colimit_obj₂_injective h) with ⟨rfl, h₁, h₂, h₃⟩ },
    unfreezingI { subst h₁, subst h₂, subst h₃ },
    exact is_colimit _ _ _ _
  end
  rfl

def comp₂ {X Y : obj₂ 𝒞} (f : hom₂ X Y) : Π {Z : obj₂ 𝒞}, hom₂ Y Z → hom₂ X Z :=
hom₂.rec_on f 
  begin
    intros X Y f Z g,
    refine hom₂_of_cat_obj_rec_on g _ _ _,
    { intros B g,
      exact of_cat_hom₂ (f ≫ g) },
    { introsI 𝒟 _ F_obj F_hom ih₁ B g ih₂,
      exact colimit_cocone_comp₂ F_obj _ _ ih₂ },
    { introsI 𝒟 _ F_obj F_hom ih₁ cone ih₂,
      exact is_limit₂ _ _ _ (λ X, ih₂ _) }
  end
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ A B f ih₂ Z g,
    refine limit_cone_comp₂ _ _ _ (ih₂ g),
  end
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ A B f ih₂ Z g,
    revert ih₂ A,
    refine hom₂_colimit_obj_rec_on g _ _ _,
    { introsI ℰ _ G_obj G_hom C ℱ _ H_obj H_hom ih₃ ih₄ A g ih₂,
      refine colimit_cocone_comp₂ _ _ _ (ih₄ _ g @ih₂) },
    { introsI ℰ _ G_obj G_hom ℱ _ H_obj H_hom ih₃ ih₄ A g ih₂,
      exact is_limit₂ _ _ _ (λ X, ih₄ _ _ g @ih₂) },
    { introsI ℰ _ G_obj G_hom cocone_obj cocone A g ih₂,
      exact ih₂ (cocone _) }
  end 
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ cone_obj cone ih₂ Z g,
    revert ih₂,
    refine hom₂_limit_obj_rec_on g _ _ _,
    { introsI ℰ _ G_obj G_hom A B g ih₂,
      exact ih₂ A g },
    { introsI ℰ _ F_obj F_hom A ℱ _ G_obj G_hom g ih₃ ih₂,
      exact colimit_cocone_comp₂ _ _ A (ih₃ @ih₂) },
    { introsI ℰ _ F_obj F_hom ℱ _ G_obj G_hom ih₃ ih₄ ih₂,
      exact is_limit₂ _ _ _ (λ X, ih₄ _ @ih₂) }
  end
  begin
    introsI 𝒟 _ F_obj F_hom ih₁ cocone_obj cocone ih₂ Z g,
    exact is_colimit₂ _ _ _ (λ A, ih₂ _ g)
  end

def UMP_obj {X Y : obj₂ 𝒞} (f : hom₂ X Y) (h : X = Y) 
  (hf : show hom ) 

end bicompletion_aux
