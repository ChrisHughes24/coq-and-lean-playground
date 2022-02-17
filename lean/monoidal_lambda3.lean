import data.vector
import data.equiv.denumerable
import data.list.sort
import ring_theory.tensor_product
import algebra.category.Module.basic

inductive type (cT : Type) : Type
| const : cT → type
| arrow : type → type → type

variables {cT : Type}

inductive term2 (ct : type cT → Type) : Π (A : type cT), Type
| const {T : type cT} (t : ct T) : term2 T
| app {T₁ T₂ : type cT} (f : term2 (T₁.arrow T₂)) (x : term2 T₁) : term2 T₂
| id {T₁ : type cT} : term2 (T₁.arrow T₁)
| comp {T₁ T₂ T₃ : type cT} : term2 ((T₁.arrow T₂).arrow ((T₂.arrow T₃).arrow (T₁.arrow T₃)))
| swap {T₁ T₂ T₃ : type cT} : term2 ((T₁.arrow (T₂.arrow T₃)).arrow (T₂.arrow (T₁.arrow T₃)))

@[derive decidable_eq] inductive type3 (cT : Type) : Type
| const : cT → type3
| arrow : type3 → type3 → type3
| id {} : type3
| tensor : type3 → type3 → type3

def type3.of_type {cT : Type} : type cT → type3 cT 
| (type.const T) := type3.const T
| (type.arrow T₁ T₂) := type3.arrow (type3.of_type T₁) (type3.of_type T₂)

inductive term3 (ct : type cT → Type) : Π (A : type3 cT), Type
| const {T : type cT} (t : ct T) : term3 (type3.of_type T)
| id (T : type3 cT) : term3 (T.arrow T)
| curry {T₁ T₂ T₃ : type3 cT} :
  term3 ((((T₁.tensor T₂).arrow T₃)).arrow (T₁.arrow (T₂.arrow T₃)))
| uncurry {T₁ T₂ T₃ : type3 cT} :
  term3 ((T₁.arrow (T₂.arrow T₃)).arrow ((T₁.tensor T₂).arrow T₃))
| tensor_map {T₁ T₂ T₃ T₄ : type3 cT} (f₁ : term3 (T₁.arrow T₃))
  (f₂ : term3 (T₂.arrow T₄)) : term3 ((T₁.tensor T₂).arrow (T₃.tensor T₄))
| tensor_symm {T₁ T₂ : type3 cT} : term3 ((T₁.tensor T₂).arrow (T₂.tensor T₁))
| lid₁ {T : type3 cT} : term3 ((type3.id.tensor T).arrow T)
| lid₂ {T : type3 cT} : term3 (T.arrow (type3.id.tensor T))
| app {T₁ T₂ : type3 cT} (f : term3 (T₁.arrow T₂)) (x : term3 T₁) : term3 T₂
| comp {T₁ T₂ T₃ : type3 cT} (f : term3 (T₁.arrow T₂)) :
  term3 ((T₂.arrow T₃).arrow (T₁.arrow T₃))

@[reducible] def context (cT : Type) : Type := list (string × type cT)

inductive term (ct : type cT → Type) : Π (Γ : context cT) (A : type cT), Type
| const {T : type cT} (t : ct T) : term [] T
| var (a : string) (T : type cT) : term [(a, T)] T
| app (Γ₁ Γ₂ : context cT) {T₁ T₂ : type cT} (f : term Γ₁ (T₁.arrow T₂)) (x : term Γ₂ T₁) : 
    term (Γ₁ ++ Γ₂) T₂
| lambda {Γ : context cT} (a : string) (T₁ : type cT) {T₂ : type cT}
    (t : term (Γ ++ [(a, T₁)]) T₂) : term Γ (T₁.arrow T₂)

def presheaf (ct : type cT → Type) : Type 1 := 
Σ (F : type cT → Type), Π {A B : type cT}, term2 ct (A.arrow B) → F A → F B

namespace presheaf

variable {ct : type cT → Type}

def hom (F G : presheaf ct) : Type :=
Π (A : type cT), F.1 A → G.1 A

def hom.comp {F G H : presheaf ct} (f : hom F G) (g : hom G H) : hom F H :=
λ A, g A ∘ f A

def hom.id (F : presheaf ct) : hom F F := λ _, id

variable (ct)

def yoneda (A : type cT) : presheaf ct := 
⟨λ B, term2 ct (A.arrow B), λ B C f g, (term2.comp.app g).app f⟩

variable {ct}

def yoneda_map {A B : type cT} (f : term2 ct (A.arrow B)) : hom (yoneda ct B) (yoneda ct A) :=
λ C, term2.app (term2.app term2.comp f)

def yoneda_full {A B : type cT} (f : hom (yoneda ct A) (yoneda ct B)) : term2 ct (B.arrow A) :=
f A term2.id

def tensor (F G : presheaf ct) : presheaf ct :=
⟨λ c, Σ c₁ c₂, F.1 c₁ × G.1 c₂ × term2 ct (c₁.arrow (c₂.arrow c)),
  -- Strictly speaking should be a colimit or something.
  λ A B f x, ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1,
     term2.app (term2.app term2.comp x.2.2.2.2)
      (term2.app (term2.app term2.swap term2.comp) f)⟩⟩

def tensor_map_left {F₁ G F₂ : presheaf ct} (f : hom F₁ F₂)  :
  hom (tensor F₁ G) (tensor F₂ G) :=
λ A a, ⟨a.1, a.2.1, f _ a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩

def tensor_map_right {F G₁ G₂ : presheaf ct} (f : hom G₁ G₂)  :
  hom (tensor F G₁) (tensor F G₂) :=
λ A a, ⟨a.1, a.2.1, a.2.2.1, f _ a.2.2.2.1, a.2.2.2.2⟩

def tensor_comm {F G : presheaf ct} : hom (tensor F G) (tensor G F) :=
λ A x, ⟨x.2.1, x.1, x.2.2.2.1, x.2.2.1, term2.swap.app x.2.2.2.2⟩

def id : presheaf ct :=
⟨λ c, term2 ct c, λ A B, term2.app⟩

def tensor_id₁ (F : presheaf ct) : hom (F.tensor id) F :=
begin
  dsimp [tensor, hom, id],
  intros A a,
  exact F.2 ((term2.swap.app a.2.2.2.2).app a.2.2.2.1) a.2.2.1
end

def tensor_id₂ (F : presheaf ct) : hom F (F.tensor id) :=
begin
  dsimp [tensor, hom, id],
  intros A a,
  refine ⟨A, A.arrow A, a, term2.id, term2.swap.app term2.id⟩,
end

/-- suspicious -/
-- lemma tensor_id (F : presheaf ct) : (tensor_id₁ F).comp (tensor_id₂ F) = hom.id _ :=
-- begin
--   funext,
--   simp [tensor_id₁, tensor_id₂],
--   dsimp [hom.comp, hom.id, tensor, id] at *,
--   ext x y,
--   dsimp, admit,
--   dsimp,

-- end
-- /-- True -/
-- lemma tensor_id' (F : presheaf ct) : (tensor_id₂ F).comp (tensor_id₁ F) = hom.id _ :=
-- begin
--   simp [tensor_id₁, tensor_id₂],
--   dsimp [hom.comp, hom.id, tensor] at *,
--   ext x y,
--   dsimp,
--   dsimp,

-- end

def id_tensor₁ (F : presheaf ct) : hom (tensor id F) F :=
begin
  dsimp [tensor, hom, id],
  intros A a,
  exact F.2 (a.2.2.2.2.app a.2.2.1) a.2.2.2.1
end

def id_tensor₂ (F : presheaf ct) : hom F (tensor id F) :=
begin
  dsimp [tensor, hom, id],
  intros A a,
  refine ⟨A.arrow A, A, term2.id, a, term2.id⟩,
end

def homp (F G : presheaf ct) : presheaf ct :=
⟨λ c, hom (tensor (yoneda ct c) F) G, begin
  intros A B f x,
  refine hom.comp _ x,
  refine tensor_map_left _,
  refine yoneda_map _,
  exact f
end⟩

def homp_map_right {F G₁ G₂ : presheaf ct} (f : hom G₁ G₂) : hom (homp F G₁) (homp F G₂) :=
begin
  dsimp [hom, homp],
  intros A x B y,
  exact f _ (x _ y)
end

def homp_map_left {F₁ F₂ G : presheaf ct} (f : hom F₁ F₂) : hom (homp F₂ G) (homp F₁ G) :=
begin
  dsimp [hom, homp],
  intros A x B y,
  refine x _ _,
  exact tensor_map_right f _ y
end

variables {F G H : presheaf ct}

def curry {F G H : presheaf ct} : hom (tensor F G) H → hom F (homp G H) :=
begin
  dsimp [homp, hom] at *,
  intros x A fA B y,
  apply x B,
  dsimp [tensor, yoneda] at *,
  use [y.1, y.2.1],
  use F.2 y.2.2.1 fA,
  use y.2.2.2.1,
  use y.2.2.2.2
end

def uncurry {F G H : presheaf ct} : hom F (homp G H) → hom (tensor F G) H :=
begin
  dsimp [tensor, hom, homp, yoneda] at *,
  intros x A y,
  refine x _ y.2.2.1 A _,
  use [y.1, y.2.1, term2.id, y.2.2.2.1, y.2.2.2.2]
end

-- Not strictly true but would be if I insisted F was actually a functor
-- def uncurry_curry' {F G H : presheaf ct} (f : (hom (tensor F G) H)) :
--   uncurry' (curry' f) = f := 
-- begin
--   dsimp [tensor, yoneda, hom, homp, curry', uncurry'] at *,
--   simp [function.funext_iff],
--   rintros a₁ a₂ ⟨_, _, _, _⟩,
--   dsimp,
-- end



end presheaf

section dpresheaf

variable (ct : type cT → Type)

def dpresheaf : Type 2 :=
Σ F : presheaf ct → Type 1, Π {A B : presheaf ct}, A.hom B → F A → F B 

namespace dpresheaf

variable {ct}

def hom (F G : dpresheaf ct) : Type 1 :=
Π (A : presheaf ct), F.1 A → G.1 A

def hom.comp {F G H : dpresheaf ct} (f : hom F G) (g : hom G H) : hom F H :=
λ A, g A ∘ f A

def hom.id (F : dpresheaf ct) : hom F F := λ _, id

variable (ct)

def yoneda (A : presheaf ct) : dpresheaf ct := 
⟨λ B, ulift (A.hom B), λ B C f ⟨g⟩, ⟨g.comp f⟩⟩

variable {ct}

def yoneda_map {A B : presheaf ct} (f : A.hom B) : hom (yoneda ct B) (yoneda ct A) :=
λ C g, ⟨f.comp g.1⟩ 

def yoneda_full {A B : presheaf ct} (f : hom (yoneda ct A) (yoneda ct B)) : B.hom A :=
(f A ⟨presheaf.hom.id _⟩).1

def tensor (F G : dpresheaf ct) : dpresheaf ct :=
⟨λ c, Σ c₁ c₂, F.1 c₁ × G.1 c₂ × (c₁.tensor c₂).hom c,
  -- Strictly speaking should be a colimit or something.
  λ A B f x, ⟨x.1, x.2.1, x.2.2.1, x.2.2.2.1, 
     begin
        refine presheaf.hom.comp x.2.2.2.2 f,
     end⟩⟩

def tensor_map_left {F₁ G F₂ : dpresheaf ct} (f : hom F₁ F₂)  :
  hom (tensor F₁ G) (tensor F₂ G) :=
λ A a, ⟨a.1, a.2.1, f _ a.2.2.1, a.2.2.2.1, a.2.2.2.2⟩

def tensor_map_right {F G₁ G₂ : dpresheaf ct} (f : hom G₁ G₂)  :
  hom (tensor F G₁) (tensor F G₂) :=
λ A a, ⟨a.1, a.2.1, a.2.2.1, f _ a.2.2.2.1, a.2.2.2.2⟩

def id : dpresheaf ct := yoneda _ presheaf.id

def tensor_id₁ (F : dpresheaf ct) : hom (F.tensor id) F :=
begin
  dsimp [hom, tensor],
  intros A x,
  apply F.2 _ x.2.2.1,
  dsimp [id, yoneda] at x,
  have := x.2.2.2.1.1,
  have := presheaf.hom.comp  
    (presheaf.tensor_map_right this) x.2.2.2.2,
  exact presheaf.hom.comp (presheaf.tensor_id₂ _) this,
end

def id_tensor₁ (F : dpresheaf ct) : hom (id.tensor F) F :=
begin
  dsimp [hom, tensor],
  intros A x,
  apply F.2 _ x.2.2.2.1,
  dsimp [id, yoneda] at x,
  have := x.2.2.1.1,
  have := presheaf.hom.comp  
    (presheaf.tensor_map_left this) x.2.2.2.2,
  exact presheaf.hom.comp (presheaf.id_tensor₂ _) this,
end

def tensor_id₂ (F : dpresheaf ct) : hom F (F.tensor id)  :=
begin
  dsimp [tensor, hom, id, yoneda],
  intros A a,
  use [A, presheaf.id, a, ⟨presheaf.hom.id _⟩],
  refine presheaf.tensor_id₁ _
end

def id_tensor₂ (F : dpresheaf ct) : hom F (tensor id F) :=
begin
 dsimp [tensor, hom, id, yoneda],
  intros A a,
  use [presheaf.id, A, ⟨presheaf.hom.id _⟩, a],
  refine presheaf.id_tensor₁ _
end

def homp (F G : dpresheaf ct) : dpresheaf ct :=
⟨λ c, hom (tensor (yoneda ct c) F) G, begin
  intros A B f x,
  refine hom.comp _ x,
  refine tensor_map_left _,
  refine yoneda_map _,
  exact f
end⟩

def homp' (F G : dpresheaf ct) : dpresheaf ct :=
⟨λ c, Σ c₁, F.1 c₁ → G.1 (c.tensor c₁), begin
  intros A B f x,
  use x.1,
  intro fx,
  refine G.2 _ (x.2 fx),
  exact presheaf.tensor_map_left f
end⟩

def homp₂ (F G : dpresheaf ct) : dpresheaf ct :=
⟨λ c, Σ c₁ c₂, (c.tensor c₁).hom c₂ → F.1 c₁ → G.1 c₂, begin admit
  -- intros A B f x,
  -- use x.1,
  -- intro fx,
  -- refine G.2 _ (x.2 fx),
  -- exact presheaf.tensor_map_left f
end⟩

variables {F G H : presheaf ct}

def curry {F G H : dpresheaf ct} : hom (tensor F G) H → hom F (homp G H) :=
begin
  dsimp [homp, hom] at *,
  intros x A fA B y,
  apply x B,
  dsimp [tensor, yoneda] at *,
  use [y.1, y.2.1],
  use F.2 y.2.2.1.1 fA,
  use y.2.2.2.1,
  use y.2.2.2.2
end

def uncurry {F G H : dpresheaf ct} : hom F (homp G H) → hom (tensor F G) H :=
begin
  dsimp [tensor, hom, homp, yoneda] at *,
  intros x A y,
  refine x _ y.2.2.1 A _,
  refine ⟨y.1, y.2.1, _, y.2.2.2.1, y.2.2.2.2⟩,
  constructor,
  exact presheaf.hom.id _
end
variable (ct)


-- Should not be using dyoneda
def dyoneda (T : type cT) : dpresheaf ct := yoneda ct (presheaf.yoneda ct T)

def eval (T : type cT) : dpresheaf ct := 
⟨λ F, ulift (F.1 T), λ A B f x, ⟨f _ x.1⟩⟩

def eval_full (T₁ T₂ : type cT) (f : hom (eval ct T₁) (eval ct T₂)) : 
  term2 ct (T₁.arrow T₂) :=
begin
  dsimp [hom, eval] at f,
  have := f (presheaf.yoneda ct T₁),
  dsimp [presheaf.yoneda] at this,
  refine (this _).1,
  exact ⟨term2.id⟩
end

variable {ct}

def dyoneda_full (T₁ T₂ : type cT) (f : hom (dyoneda ct T₁) (dyoneda ct T₂)) : 
  term2 ct (T₁.arrow T₂) := presheaf.yoneda_full $ yoneda_full f

def tensor_hom (A B : type cT) : presheaf ct :=
⟨λ C, term2 ct (A.arrow (B.arrow C)), 
  λ C D f g,begin
    refine (term2.comp.app g).app _,
    refine (term2.swap.app term2.comp).app f,
  end⟩

def eval_tensor (T₁ T₂ T₃ : type cT) : hom (tensor (eval ct T₁) (eval ct T₂)) (eval ct T₃) → 
  term2 ct (T₁.arrow (T₂.arrow T₃)) :=
begin
  dsimp [eval, yoneda, homp', homp₂, hom, tensor] at *,
  intros x,
  refine (x (tensor_hom T₁ T₂) _).1,
  dsimp [presheaf.hom],
  use [presheaf.yoneda ct T₁, presheaf.yoneda ct T₂, ⟨term2.id⟩, ⟨term2.id⟩],
  dsimp [presheaf.yoneda, presheaf.tensor, tensor_hom],
  intros A y,
  refine (term2.comp.app ((term2.comp.app y.2.2.1).app y.2.2.2.2)).app _,
  refine term2.comp.app y.2.2.2.1
end

def eval_homp₂ (T₁ T₂ : type cT) : hom (homp' (eval ct T₁) (eval ct T₂)) 
  (eval ct (T₁.arrow T₂)) :=
begin
  dsimp [eval, yoneda, homp', homp₂, hom] at *,
  intros F x,
  split,
  rcases x with ⟨G, _⟩,
  split,
  

end

def _homp (T₁ T₂ : type cT) : hom (homp (dyoneda ct T₁) (dyoneda ct T₂)) 
  (dyoneda ct (T₁.arrow T₂)) :=
begin
  intros F a,
  split,
  dsimp [presheaf.yoneda, presheaf.hom, dyoneda, yoneda, homp, tensor, hom] at *,
  intros A f,
  refine (a F _).1 _ _,
  { use F,
    use presheaf.yoneda ct T₁,
    use λ _ x, x,
    use λ _ x, x,
    intros B x,
    delta presheaf.tensor presheaf.yoneda at x,
    dsimp at x,
     admit },
  { 
    refine (term2.comp.app _).app f,
      }

end
def dyoneda_homp' (T₁ T₂ : type cT) : hom 
  (dyoneda ct (T₁.arrow T₂))
  (homp (dyoneda ct T₁) (dyoneda ct T₂))  :=
begin
   dsimp [presheaf.yoneda, presheaf.hom, dyoneda, yoneda, homp, tensor, hom] at *,
   intros F x G y,
   split,
   intros A f,
  

end

end dpresheaf
end dpresheaf

open category_theory

section

def contexti : context cT → type3 cT
| []       := type3.id
| (T :: l) := type3.tensor (type3.of_type T.2) (contexti l)

namespace term3 

variables {ct : type cT → Type}

def tensor_mk {T₁ T₂ : type3 cT} : term3 ct (T₁.arrow (T₂.arrow (T₁.tensor T₂))) := 
term3.app term3.curry (term3.id _)

def rid₁ {T : type3 cT} : term3 ct ((T.tensor type3.id).arrow T) :=
term3.app (term3.comp term3.tensor_symm) term3.lid₁

def rid₂ (T : type3 cT) : term3 ct (T.arrow (T.tensor type3.id)) :=
term3.app (term3.comp term3.lid₂) term3.tensor_symm

def lift {T : type3 cT} : term3 ct (T.arrow (type3.id.arrow T)) :=
term3.app term3.curry term3.rid₁

def drop {T : type3 cT} : term3 ct ((type3.id.arrow T).arrow T) :=
term3.app (term3.comp (term3.rid₂ _)) 
  (term3.app (term3.uncurry) (term3.id _))

def assoc₁ {T₁ T₂ T₃ : type3 cT} : 
  term3 ct (((T₁.tensor T₂).tensor T₃).arrow (T₁.tensor (T₂.tensor T₃))) :=
term3.app term3.uncurry $ term3.app term3.uncurry $
  term3.app (term3.comp term3.tensor_mk) term3.curry

def assoc₂ {T₁ T₂ T₃ : type3 cT} :
  term3 ct ((T₁.tensor (T₂.tensor T₃)).arrow ((T₁.tensor T₂).tensor T₃)) :=
term3.app term3.uncurry $ term3.app (term3.comp 
  (term3.app term3.curry tensor_mk)) term3.uncurry

def contexti_append₁ : Π (Γ₁ Γ₂ : context cT), term3 ct 
  ((contexti (Γ₁ ++ Γ₂)).arrow ((contexti Γ₁).tensor (contexti Γ₂)))
| []      Γ₂ := lid₂
| (T::Γ₁) Γ₂ := term3.app (term3.comp (term3.tensor_map (term3.id _) 
  (contexti_append₁ _ _))) term3.assoc₂
 
def contexti_append₂ : Π (Γ₁ Γ₂ : context cT), term3 ct 
  (((contexti Γ₁).tensor (contexti Γ₂)).arrow (contexti (Γ₁ ++ Γ₂)))
| []      Γ₂ := lid₁
| (T::Γ₁) Γ₂ := term3.app (term3.comp term3.assoc₁) 
  (term3.tensor_map (term3.id _) (contexti_append₂ _ _))

open dpresheaf

def type3_to_dpresheaf : Π (T : type3 cT), dpresheaf ct
| (type3.const T)      := dpresheaf.dyoneda ct (type.const T)
| (type3.arrow T₁ T₂)  := dpresheaf.homp (type3_to_dpresheaf T₁) (type3_to_dpresheaf T₁)
| (type3.tensor T₁ T₂) := dpresheaf.tensor (type3_to_dpresheaf T₁) (type3_to_dpresheaf T₂)
| (type3.id)           := dpresheaf.id

def term3_to_dpresheaf : Π (T : type3 cT) (t : term3 ct T), dpresheaf ct

end term3

variables {ct : type cT → Type}
variables (cti : Π {T : type cT}, ct T → type3 cT)

def termi : Π {Γ : context cT} {A : type cT} (t : term ct Γ A),
  term3 ct ((contexti Γ).arrow (type3.of_type A))
| _ A (term.const t) := term3.app term3.lift (term3.const t)
| _ _ (term.var _ A) :=  term3.rid₁
| _ T₂ (@term.app  _ _ Γ₁ Γ₂ T₁ _ f x) := 
term3.app (term3.comp (term3.contexti_append₁ _ _)) 
  (term3.app term3.uncurry 
    (term3.app (term3.comp (termi f)) 
      (term3.comp (termi x))))
| Γ (type.arrow _ T₂) (term.lambda a T₁ t) :=
term3.app term3.curry 
  (term3.app (term3.comp 
    (term3.app (term3.comp (term3.tensor_map (term3.id _) 
        (term3.rid₂ _))) (term3.contexti_append₂ Γ [(a, T₁)]))) (termi t))


end
