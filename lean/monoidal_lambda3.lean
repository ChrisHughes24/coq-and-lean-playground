import data.vector
import data.equiv.denumerable
import data.list.sort
import ring_theory.tensor_product
import algebra.category.Module.basic

@[derive has_reflect] inductive type (cT : Type) : Type
| const : cT → type
| arrow : type → type → type

variables {cT : Type}

inductive term2 (ct : type cT → Type) : Π (A : type cT), Type
| const {T : type cT} (t : ct T) : term2 T
| app {T₁ T₂ : type cT} (f : term2 (T₁.arrow T₂)) (x : term2 T₁) : term2 T₂
| id {T₁ : type cT} : term2 (T₁.arrow T₁)
| comp {T₁ T₂ T₃ : type cT} : term2 ((T₁.arrow T₂).arrow ((T₂.arrow T₃).arrow (T₁.arrow T₃)))
| swap {T₁ T₂ T₃ : type cT} : term2 ((T₁.arrow (T₂.arrow T₃)).arrow (T₂.arrow (T₁.arrow T₃)))

-- def term2.reflect (ct : type cT → Type) [Π A, has_reflect (ct A)] [reflected cT] [reflected ct] : 
--   Π {A : type cT}, term2 ct A → expr
-- | _ (term2.const t) := _
-- | _ (term2.app f x) := _

-- def simplify {ct : type cT → Type} : Π {T₁ : type cT}, term2 ct T₁ → term2 ct T₁
-- | _ (term2.app term2.comp term2.id) := term2.id
-- | _ (term2.app term2.id x) := x
-- | _ (term2.app term2.swap (term2.app term2.swap f)) := f
-- | _ (term2.app (term2.app (term2.app term2.comp f) g) x) := term2.app g (term2.app f x)
-- | _ (term2.app (term2.app term2.comp f) term2.id) := f
-- | _ (term2.app (term2.app term2.swap term2.comp) term2.id) := term2.id
-- | _ x := x

namespace term2

variables {ct : type cT → Type} {T₁ T₂ T₃ : type cT}

def comp' : Π {T₁ T₂}

-- def app' : Π {T₁ T₂ : type cT} (f : term2 ct (T₁.arrow T₂)) (x : term2 ct T₁), term2 ct T₂
-- | _ _ (const f) x := (const f).app x
-- | _ _ (app f x) y := (app f x).app y
-- | _ _ term2.id  x := x
-- | _ _ (term2.app (term2.app term2.comp f) g) x := app' g (app' f x)
-- | _ _ f x := f.app x
-- using_well_founded { dec_tac := `[admit] }

end term2

@[reducible] def context (cT : Type) : Type := list (string × type cT)

inductive term (ct : type cT → Type) : Π (Γ : context cT) (A : type cT), Type
| const {T : type cT} (t : ct T) : term [] T
| var (a : string) (T : type cT) : term [(a, T)] T
| app (Γ₁ Γ₂ : context cT) {T₁ T₂ : type cT} (f : term Γ₁ (T₁.arrow T₂)) (x : term Γ₂ T₁) : term (Γ₂ ++ Γ₁) T₂
| lambda {Γ : context cT} (a : string) (T₁ : type cT) {T₂ : type cT}
    (t : term ((a, T₁) :: Γ) T₂) : term Γ (T₁.arrow T₂)

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

def alpha {A B C D X : type cT}
  (f : term2 ct (A.arrow (B.arrow X)))
  (g : term2 ct (X.arrow (C.arrow D))) :
  Σ Y : type cT, 
    term2 ct (B.arrow (C.arrow Y)) × term2 ct (A.arrow (Y.arrow D)) :=
begin
  have h : term2 ct (A.arrow (B.arrow (C.arrow D))),
  { refine (term2.comp.app f).app _,
    refine (term2.swap.app term2.comp).app g },
  have h' : term2 ct (B.arrow (C.arrow (A.arrow D))),
  { refine (term2.comp.app _).app term2.swap,
    refine term2.swap.app h },
  use (A.arrow D),
  use h',
  use term2.swap.app term2.id
end

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

def rid₁ (F : presheaf ct) : hom (F.tensor id) F :=
begin
  dsimp [tensor, hom, id],
  intros A a,
  exact F.2 ((term2.swap.app a.2.2.2.2).app a.2.2.2.1) a.2.2.1
end

def rid₂ (F : presheaf ct) : hom F (F.tensor id) :=
begin
  dsimp [tensor, hom, id],
  intros A a,
  refine ⟨A, A.arrow A, a, term2.id, term2.swap.app term2.id⟩,
end

def lid₁ (F : presheaf ct) : hom (tensor id F) F :=
begin
  dsimp [tensor, hom, id],
  intros A a,
  exact F.2 (a.2.2.2.2.app a.2.2.1) a.2.2.2.1
end

def lid₂ (F : presheaf ct) : hom F (tensor id F) :=
begin
  dsimp [tensor, hom, id],
  intros A a,
  refine ⟨A.arrow A, A, term2.id, a, term2.id⟩,
end

def homp (F G : presheaf ct) : presheaf ct :=
⟨λ c, Π c₁ c₂ : type cT, term2 ct (c.arrow (c₁.arrow c₂)) → F.1 c₁ → G.1 c₂,
begin
  intros A B f x c₁ c₂ g Fc,
  specialize x c₁ c₂ ((term2.comp.app f).app g) Fc,
  exact x
end⟩

def comp {F G H : presheaf ct} : hom (homp G H) (homp (homp F G) (homp F H)) :=
begin
  intros A x,
  dsimp [homp] at *,
  intros c₁ c₂ f h c₃ c₄ g Fc₃,
  have := alpha f g,
  apply x _ _ this.2.2,
  apply h,
  apply this.2.1,
  exact Fc₃
end

def scomp {F G H : presheaf ct} : hom (homp F G) (homp (homp G H) (homp F H)) :=
begin
  intros A x,
  dsimp [homp] at *,
  intros c₁ c₂ f h c₃ c₄ g Fc₃,
  have := alpha (term2.swap.app f) g,
  apply h _ _ this.2.2,
  apply x,
  apply this.2.1,
  exact Fc₃
end

def tensor_mk {F G : presheaf ct} : hom F (homp G (F.tensor G)) :=
begin
  intros A FA c₁ c₂ f Gc₁,
  dsimp [homp, tensor],
  exact ⟨_, _, FA, Gc₁, f⟩
end

def curry {F G H : presheaf ct} : (F.tensor G).hom H → F.hom (G.homp H) :=
begin
  intros x A FA c₁ c₂ f Gc₁,
  dsimp [homp, tensor, hom] at *,
  apply x,
  refine ⟨_, _, _, _, f⟩,
  exact FA,
  exact Gc₁
end

def thing {A B C D : presheaf ct} (f : hom A (homp B C)) :
  hom (homp C D) (homp A (homp B D)) :=  
begin
  intros c₁ x c₂ c₃ h Ac₂ c₄ c₅ i Bc₄,
  dsimp [homp] at x,
  have := alpha h i,
  apply x,
  exact this.2.2,
  apply f,
  exact Ac₂,
  exact this.2.1,
  exact Bc₄
end

def lcurry {F G H : presheaf ct} : hom (homp (tensor F G) H) (homp F (homp G H)) :=
begin
  apply thing,
  exact tensor_mk
end

def uncurry {F G H : presheaf ct} : F.hom (G.homp H) → (F.tensor G).hom H :=
begin
  intros x A FGA,
  dsimp [homp, tensor, hom] at *,
  apply x _ FGA.2.2.1 _ _ _ FGA.2.2.2.1,
  exact FGA.2.2.2.2
end
universes u v w x
def Day (F : Type u → Type v) (G : Type w → Type x) : Type* → Type* :=
λ A, Σ (B : Type u) (C : Type w), F B × G C × (B → C → A)

def assoc₁ {F G H : presheaf ct} : hom ((F.tensor G).tensor H) (F.tensor (G.tensor H)) :=
uncurry (uncurry (hom.comp tensor_mk lcurry))
-- ⟨x.snd.snd.snd.fst.snd.fst.arrow A,
--    ⟨x.snd.snd.snd.fst.snd.fst,
--     (⟨x.fst,
--       ⟨x.snd.snd.snd.fst.fst,
--        (x.snd.snd.fst,
--         x.snd.snd.snd.fst.snd.snd.fst,
--         term2.swap.app
--           ((term2.comp.app
--               (term2.swap.app
--                  ((term2.comp.app (term2.swap.app x.snd.snd.snd.fst.snd.snd.snd.snd)).app
--                     ((term2.swap.app term2.comp).app (term2.swap.app x.snd.snd.snd.snd))))).app
--              term2.swap))⟩⟩,
--      x.snd.snd.snd.fst.snd.snd.snd.fst,
--      term2.swap.app (term2.swap.app term2.id))⟩⟩
def assoc₂ {F G H : presheaf ct} : hom (F.tensor (G.tensor H)) ((F.tensor G).tensor H) :=
begin
  rintros A ⟨B, C, fb, ⟨D, E, gd, he, dec⟩, bca⟩,
  refine ⟨E.arrow A, E, ⟨B, D, fb, gd, _⟩, he, term2.id⟩,
  refine (term2.comp.app bca).app _,
  refine (term2.comp.app _).app (term2.comp.app dec),
  refine term2.swap.app term2.comp
end

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

def tensor_comm {F G : dpresheaf ct} : hom (tensor F G) (tensor G F) :=
begin
  intro A,
  rintro ⟨c₁, c₂, Fc₁, Gc₂, f⟩,
  exact ⟨c₂, c₁, Gc₂, Fc₁, presheaf.hom.comp presheaf.tensor_comm f⟩
end
 

def assoc₁ {F G H : dpresheaf ct} : hom ((F.tensor G).tensor H) (F.tensor (G.tensor H))  :=
begin
  intro A,
  rintros ⟨E, D, ⟨B, C, fb, gc, bce⟩, hd, eda⟩,
  refine ⟨B, C.tensor D, fb, ⟨C, D, gc, hd, presheaf.hom.id _⟩, _⟩, 
  refine presheaf.assoc₂.comp _,
  refine (presheaf.tensor_map_left _).comp eda,
  exact bce 
end

def assoc₂ {F G H : dpresheaf ct} : hom (F.tensor (G.tensor H)) ((F.tensor G).tensor H) :=
begin
  intro A,
  rintros ⟨B, C, fb, ⟨D, E, gd, he, dec⟩, bca⟩,
  refine ⟨_, _, ⟨_, _, fb, gd, presheaf.hom.id _⟩, he, _⟩,
  refine presheaf.hom.comp _ bca,
  refine presheaf.hom.comp presheaf.assoc₁ _,
  refine presheaf.tensor_map_right dec
end

def id : dpresheaf ct := yoneda _ presheaf.id

def rid₁ (F : dpresheaf ct) : hom (F.tensor id) F :=
begin
  dsimp [hom, tensor],
  intros A x,
  apply F.2 _ x.2.2.1,
  dsimp [id, yoneda] at x,
  have := x.2.2.2.1.1,
  have := presheaf.hom.comp  
    (presheaf.tensor_map_right this) x.2.2.2.2,
  exact presheaf.hom.comp (presheaf.rid₂ _) this,
end

def lid₁ (F : dpresheaf ct) : hom (id.tensor F) F :=
begin
  dsimp [hom, tensor],
  intros A x,
  apply F.2 _ x.2.2.2.1,
  dsimp [id, yoneda] at x,
  have := x.2.2.1.1,
  have := presheaf.hom.comp  
    (presheaf.tensor_map_left this) x.2.2.2.2,
  exact presheaf.hom.comp (presheaf.lid₂ _) this,
end

def rid₂ (F : dpresheaf ct) : hom F (F.tensor id)  :=
begin
  dsimp [tensor, hom, id, yoneda],
  intros A a,
  use [A, presheaf.id, a, ⟨presheaf.hom.id _⟩],
  refine presheaf.rid₁ _
end

def lid₂ (F : dpresheaf ct) : hom F (tensor id F) :=
begin
 dsimp [tensor, hom, id, yoneda],
  intros A a,
  use [presheaf.id, A, ⟨presheaf.hom.id _⟩, a],
  refine presheaf.lid₁ _
end

def homp (F G : dpresheaf ct) : dpresheaf ct :=
⟨λ c, hom (tensor (yoneda ct c) F) G, begin
  intros A B f x,
  refine hom.comp _ x,
  refine tensor_map_left _,
  refine yoneda_map _,
  exact f
end⟩

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

def lcurry_aux {A F G H : dpresheaf ct} : (hom A (homp (tensor F G) H)) → (hom A (homp F (homp G H))) :=
begin
  intro f,
  refine curry _,
  refine curry _,
  refine assoc₁.comp _,
  refine uncurry _,
  exact f
end

def lcurry {F G H : dpresheaf ct} : hom (homp (tensor F G) H) (homp F (homp G H)) :=
lcurry_aux (hom.id _)

def luncurry_aux {A F G H : dpresheaf ct} : (hom A (homp F (homp G H))) → (hom A (homp (tensor F G) H)) :=
begin
  intro f,
  refine curry _,
  refine assoc₂.comp _,
  refine uncurry _,
  refine uncurry _,
  exact f,
end

def luncurry {F G H : dpresheaf ct} : hom (homp F (homp G H)) (homp (tensor F G) H) :=
luncurry_aux (hom.id _)

def lcomp {F G H : dpresheaf ct} : hom (homp F G) (homp (homp G H) (homp F H)) :=
begin
  refine curry _,
  refine curry _,
  refine (tensor_map_left tensor_comm).comp _,
  refine assoc₁.comp _,
  refine (tensor_map_right (uncurry (hom.id _))).comp _,
  refine uncurry _,
  exact hom.id _
end

def homp_map_left {F G H : dpresheaf ct} (f : hom G H) : hom (homp H F) (homp G F) := 
begin
  intros A,
  dsimp [homp],
  intro g,
  refine hom.comp (tensor_map_right f) g,
end

def homp_map_right {F G H : dpresheaf ct} (f : hom G H) : hom (homp F G) (homp F H) := 
begin
  intros A,
  dsimp [homp],
  intro g,
  refine hom.comp g f,
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

def eval_tensor₁ (T₁ T₂ T₃ : type cT) : 
  hom (tensor (eval ct T₁) (eval ct T₂)) (eval ct T₃) → 
  term2 ct (T₁.arrow (T₂.arrow T₃)) :=
begin
  dsimp [eval, yoneda, hom, tensor] at *,
  intros x,
  refine (x (tensor_hom T₁ T₂) _).1,
  dsimp [presheaf.hom],
  use [presheaf.yoneda ct T₁, presheaf.yoneda ct T₂, ⟨term2.id⟩, ⟨term2.id⟩],
  dsimp [presheaf.yoneda, presheaf.tensor, tensor_hom],
  intros A y,
  refine (term2.comp.app ((term2.comp.app y.2.2.1).app y.2.2.2.2)).app _,
  refine term2.comp.app y.2.2.2.1
end

def eval_tensor₂ (T₁ T₂ T₃ : type cT) : 
  term2 ct (T₁.arrow (T₂.arrow T₃)) → 
  hom (tensor (eval ct T₁) (eval ct T₂)) (eval ct T₃) :=
begin
  dsimp [eval, yoneda, hom, tensor] at *,
  intros f A y,
  dsimp [presheaf.tensor, presheaf.hom] at *,
  split,
  apply y.2.2.2.2,
  use [T₁, T₂, y.2.2.1.1, y.2.2.2.1.1, f]
end

def thing (A : presheaf ct) (B : type cT) : presheaf ct :=
⟨λ C, A.1 (B.arrow C), 
  λ C D f g,begin
    refine A.2 _ g,
    refine (term2.swap.app term2.comp).app f
  end⟩

def eval_homp₁ (T₁ T₂ : type cT) : 
  hom (homp (eval ct T₁) (eval ct T₂)) (eval ct (T₁.arrow T₂)) :=
begin
  intro A,
  dsimp [homp, eval, yoneda, tensor, hom],
  intro x,
  refine x (thing _ _) _,
  use A,
  use (presheaf.yoneda ct T₁),
  use ⟨presheaf.hom.id _⟩,
  use ⟨term2.id⟩,
  dsimp [presheaf.tensor, presheaf.yoneda, thing, presheaf.hom],
  rintros B ⟨c₁, c₂, Ac₁, g, f⟩,
  have h : term2 ct (c₁.arrow (T₁.arrow B)),
  { refine (term2.comp.app f).app _,
    refine term2.comp.app _,
    exact g },
  exact A.2 h Ac₁
end

def eval_homp₂ (T₁ T₂ : type cT) : 
  hom (eval ct (T₁.arrow T₂)) (homp (eval ct T₁) (eval ct T₂)) :=
begin
  refine curry _,
  refine eval_tensor₂ _ _ _ _,
  exact term2.id
end



open category_theory

def contexti : context cT → dpresheaf ct
| []       := dpresheaf.id
| (T :: l) := tensor (contexti l) (eval ct T.2)

def lift {T : dpresheaf ct} : hom T (homp id T) :=
curry (hom.comp (rid₁ _) (hom.id _))

def drop {T : dpresheaf ct} : hom (homp id T) T :=
hom.comp (rid₂ _) (uncurry (hom.id _))

def contexti_append₁ : Π (Γ₁ Γ₂ : context cT), hom 
  (contexti (Γ₂ ++ Γ₁))  ((contexti Γ₁).tensor (@contexti _ ct Γ₂))
| Γ₁      [] := rid₂ _
| Γ₁ (T::Γ₂) := hom.comp (tensor_map_left (contexti_append₁ _ _)) assoc₁
 
def contexti_append₂ : Π (Γ₁ Γ₂ : context cT), hom 
  ((contexti Γ₁).tensor (contexti Γ₂)) (@contexti _ ct (Γ₂ ++ Γ₁))
| Γ₁      [] := rid₁ _
| Γ₁ (T::Γ₂) := hom.comp assoc₂ (tensor_map_left (contexti_append₂ _ _))

open dpresheaf

@[reducible] def termi : Π {Γ : context cT} {A : type cT} (t : term ct Γ A),
  hom (@contexti _ ct Γ) (eval ct A)
| _ A (term.const t) := λ F x, ⟨x.1 _ (term2.const t)⟩
| _ _ (term.var _ A) := lid₁ _
| _ T₂ (@term.app  _ _ Γ₁ Γ₂ T₁ _ f x) := 
hom.comp (contexti_append₁ _ _) (uncurry (hom.comp (termi f) 
   ((eval_homp₂ _ _).comp $ homp_map_left (termi x))))
| Γ (type.arrow _ T₂) (term.lambda a T₁ t) := 
  hom.comp (curry (termi t)) (eval_homp₁ _ _)

end dpresheaf

end dpresheaf

open term

open category_theory
open_locale tensor_product

variable {ct : type cT → Type}

def term_to_term2 {A : type cT} (t : term ct [] A) : term2 ct A :=
(dpresheaf.termi t (presheaf.id) ⟨presheaf.hom.id _⟩).1

variables {R : Type} [comm_ring R] 

def typei (cTi : cT → Module.{0 0} R) : type cT → Module R
| (type.const T)     := cTi T
| (type.arrow T₁ T₂) := Module.of R (typei T₁ →ₗ[R] typei T₂)

-- inductive term2 (ct : type cT → Type) : Π (A : type cT), Type
-- | const {T : type cT} (t : ct T) : term2 T
-- | app {T₁ T₂ : type cT} (f : term2 (T₁.arrow T₂)) (x : term2 T₁) : term2 T₂
-- | id {T₁ : type cT} : term2 (T₁.arrow T₁)
-- | comp {T₁ T₂ T₃ : type cT} : term2 ((T₁.arrow T₂).arrow ((T₂.arrow T₃).arrow (T₁.arrow T₃)))
-- | swap {T₁ T₂ T₃ : type cT} : term2 ((T₁.arrow (T₂.arrow T₃)).arrow (T₂.arrow (T₁.arrow T₃)))

def linear_map.swap {R M N P : Type*} [comm_semiring R] [add_comm_monoid M]
  [add_comm_monoid N] [add_comm_monoid P] [module R M] [module R N] [module R P]
  : (M →ₗ[R] N →ₗ[R] P) →ₗ[R] (N →ₗ[R] M →ₗ[R] P) :=
{ to_fun := λ f,
  { to_fun := λ n,
    { to_fun := λ m, f m n,
      map_add' := λ _ _, by rw [f.map_add]; refl,
      map_smul' := λ _ _, by rw [f.map_smul]; refl, },
    map_add' := λ _ _, by simp only [(f _).map_add]; refl,
    map_smul' := λ _ _, by simp only [(f _).map_smul]; refl },
  map_add' := λ _ _, rfl,
  map_smul' := λ _ _, rfl }

local attribute [reducible] typei

def termi (cTi : cT → Module.{0 0} R) (const_term : Π {A}, ct A → typei cTi A) :
  Π {A : type cT}, term2 ct A → typei cTi A
| T (term2.const x) := const_term x
| _ (term2.app f x) := begin 
  have := termi f,
  dsimp [typei] at this,
  exact this (termi x),
end
| _ (term2.id) := linear_map.id
| _ (term2.comp) := linear_map.swap (linear_map.llcomp _ _ _ _)
| _ (term2.swap) := linear_map.swap


def const_term : type unit → Type
| (type.arrow (type.const ()) (type.arrow (type.const ()) (type.const ()))) := unit
| _ := empty

variables (M : Module.{0 0} R) (op : M →ₗ[R] M →ₗ[R] M)

def cTi : unit → Module R := λ _, M

include op

def const_termi {T : type unit} (t : const_term T) : typei (@cTi R _ M) T :=
begin
  cases T with _ T₁ T₂; try { apply empty.elim t },
  cases T₁ with _ T₂ T₃; try { apply empty.elim t },
  cases T₁,
  cases T₂ with _ T₁ T₂; try { apply empty.elim t },
  cases T₁ with _ T₁ T₂; try { apply empty.elim t },
  cases T₁,
  cases T₂ with _ T₁ T₂; try { apply empty.elim t },
  exact op
end

omit op

def mult : const_term (type.arrow (type.const ()) (type.arrow (type.const ()) (type.const ()))) := ()

notation `T` := type.const ()

def exmpl₁ : @term unit const_term [] 
  ((type.const ()).arrow ((type.const ()).arrow ((type.const ()).arrow (type.const ())))) :=
lambda "a" T $ 
lambda "b" T $
lambda "c" T $
  app [("a", T), ("b", T)].reverse [("c", T)] 
  (app [] [("a", T), ("b", T)].reverse (const mult) 
    (app [("a", T)] [("b", T)] 
      (app [] [("a", T)] (const mult) (var "a" (type.const ()))) 
        (var "b" (type.const ()))) : _) 
    (var "c" (type.const ()))

#reduce (term_to_term2 exmpl₁)

example (p q r : M) : 
  (((termi (@cTi R _ M) (@const_termi _ _ _ op) (term_to_term2 exmpl₁)).to_fun p).to_fun q).to_fun r = 
  op (op p q) r :=
begin
  refl
end

def exmpl₂ : @term unit const_term [] 
  ((type.const ()).arrow ((type.const ()).arrow ((type.const ()).arrow (type.const ())))) :=
lambda "a" T $ 
lambda "b" T $
lambda "c" T $
  (app [("a", T)] [("b", T), ("c", T)].reverse
  (app [] [("a", T)] (const mult) (var "a" (type.const ())) : _) 
    (app [("b", T)] [("c", T)] 
      (app [] [("b", T)] (const mult) (var "b" (type.const ()))) 
        (var "c" (type.const ())))  : _)

#reduce (term_to_term2 exmpl₂)

example (p q r : M) : 
  (((termi (@cTi R _ M) (@const_termi _ _ _ op) (term_to_term2 exmpl₂)).to_fun p).to_fun q).to_fun r = 
  op p (op q r) :=
begin
  refl,
end

notation ` bin_op ` :=  ((type.const ()).arrow ((type.const ()).arrow (type.const ())))

def exmpl₃ : @term unit const_term [] 
  (type.arrow bin_op ((type.const ()).arrow ((type.const ()).arrow ((type.const ()).arrow (type.const ()))))) :=
lambda "o" bin_op $
lambda "a" T $ 
lambda "b" T $
lambda "c" T $
  app [("o", bin_op), ("a", T), ("b", T)].reverse [("c", T)] 
  (app [("o", bin_op)] [("a", T), ("b", T)].reverse (var "o" bin_op) 
    (app [("a", T)] [("b", T)] 
      (app [] [("a", T)] (const mult) (var "a" (type.const ()))) 
        (var "b" (type.const ()))) : _) 
    (var "c" (type.const ()))

example (p q r : M) (op1 : M →ₗ[R] M →ₗ[R] M): 
  ((((termi (@cTi R _ M) (@const_termi _ _ _ op) (term_to_term2 exmpl₃)).to_fun op1).to_fun p).to_fun q).to_fun r = 
  op1 (op p q) r :=
begin
  refl,

  -- dsimp [termi, const_termi, cTi, term_to_term2, dpresheaf.termi, exmpl₃, dpresheaf.eval, dpresheaf.eval_homp₁,
  --   dpresheaf.eval_homp₂, dpresheaf.contexti, dpresheaf.contexti_append₂, dpresheaf.contexti_append₁,
  --   dpresheaf.eval_tensor₁, dpresheaf.eval_tensor₂, presheaf.alpha, typei, context, list.reverse, list.append, list.reverse_core,

  --   dpresheaf.tensor, dpresheaf.tensor_map_left, dpresheaf.yoneda, dpresheaf.id, dpresheaf.thing,
  --   dpresheaf.tensor_map_right, dpresheaf.tensor_comm, dpresheaf.homp, dpresheaf.rid₁, dpresheaf.lid₁,
  --   dpresheaf.lid₂, dpresheaf.rid₂, dpresheaf.curry, dpresheaf.uncurry, dpresheaf.hom, dpresheaf.hom.id,
  --   dpresheaf.hom.comp, dpresheaf.homp_map_left, dpresheaf.homp_map_right, dpresheaf.assoc₁, dpresheaf.assoc₂,
    
  --   presheaf.tensor, presheaf.tensor_map_left, presheaf.yoneda, presheaf.id, presheaf.thing,
  --   presheaf.tensor_map_right, presheaf.tensor_comm, presheaf.homp, presheaf.rid₁, presheaf.lid₁,
  --   presheaf.lid₂, presheaf.rid₂, presheaf.curry, presheaf.uncurry, presheaf.hom, presheaf.hom.id,
  --   presheaf.hom.comp, presheaf.assoc₁, presheaf.assoc₂,

  --   linear_map.swap, linear_map.comp, linear_map.llcomp, linear_map.lcomp, linear_map.id],
  -- simp,
end