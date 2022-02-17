import data.vector
import data.equiv.denumerable
import data.list.sort
import ring_theory.tensor_product
import algebra.category.Module.basic

@[derive decidable_eq] inductive type (cT : Type) : Type
| const : cT → type
| arrow : type → type → type

variables (cT : Type)

@[reducible] def context (cT : Type) : Type := list (string × type cT)

-- instance : has_append (context cT) :=
-- ⟨λ a b : list (string × type cT), list.append b a⟩

variables {cT}

inductive term (ct : type cT → Type) : Π (Γ : context cT) (A : type cT), Type
| const {T : type cT} (t : ct T) : term [] T
| var (a : string) (T : type cT) : term [(a, T)] T
| app (Γ₁ Γ₂ : context cT) {T₁ T₂ : type cT} (f : term Γ₁ (T₁.arrow T₂)) (x : term Γ₂ T₁) : 
    term (Γ₁ ++ Γ₂) T₂
| lambda {Γ : context cT} (a : string) (T₁ : type cT) {T₂ : type cT}
    (t : term (Γ ++ [(a, T₁)]) T₂) : term Γ (T₁.arrow T₂)

inductive term2 (ct : type cT → Type) : Π (A : type cT), Type
| const {T : type cT} (t : ct T) : term2 T
| app {T₁ T₂ : type cT} (f : term2 (T₁.arrow T₂)) (x : term2 T₁) : term2 T₂
| id {T₁ : type cT} : term2 (T₁.arrow T₁)
| comp {T₁ T₂ T₃ : type cT} : term2 ((T₁.arrow T₂).arrow ((T₂.arrow T₃).arrow (T₁.arrow T₃)))
| swap {T₁ T₂ T₃ : type cT} : term2 ((T₁.arrow (T₂.arrow T₃)).arrow (T₂.arrow (T₁.arrow T₃)))

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
⟨λ B, term2 ct (A.arrow B), λ B C f g, term2.app (term2.app term2.comp g) f⟩

variable {ct}

def yoneda_map {A B : type cT} (f : term2 ct (A.arrow B)) : hom (yoneda ct B) (yoneda ct A) :=
λ C, term2.app (term2.app term2.comp f)

def yoneda_full {A B : type cT} (f : hom (yoneda ct B) (yoneda ct A)) : 
  term2 ct (A.arrow B) :=
f B term2.id

def sumthing (F : presheaf ct) : presheaf ct :=
⟨λ c, Σ c' : type cT, term2 ct (c'.arrow c) × F.1 c', 
  λ A B f a, ⟨a.1, (term2.app term2.comp a.2.1).app f, a.2.2⟩⟩

def to_sumthing (F : presheaf ct) : hom F (sumthing F) :=
λ A a, ⟨A, term2.id, a⟩

def of_sumthing (F : presheaf ct) : hom (sumthing F) F :=
λ A b, F.2 b.2.1 b.2.2

def tensor (F G : presheaf ct) : presheaf ct :=
⟨λ c, Σ c₁ c₂ : type cT, term2 ct (c₁.arrow (c₂.arrow c)) × F.1 c × G.1 c, 
  λ A B f x, ⟨x.1, x.2.1, term2.app (term2.app term2.comp x.2.2.1) 
      (term2.app (term2.app term2.swap term2.comp) f), 
    F.2 f x.2.2.2.1, G.2 f x.2.2.2.2⟩⟩

def tensor_assoc₁ (F G H : presheaf ct) : 
  hom (tensor (tensor F G) H) (tensor F (tensor G H)) :=
λ A a, begin
  rcases a with ⟨c₁, c₂, h₁, ⟨c₃, c₄, h₂, f, g⟩, h⟩,
  exact ⟨c₁, c₂, h₁, f, c₃, c₄, h₂, g, h⟩
end

def tensor_assoc (F G H : presheaf ct) : 
  hom (tensor F (tensor G H)) (tensor (tensor F G) H) :=
λ A a, begin
  rcases a with ⟨c₁, c₂, h₁, f, c₃, c₄, h₂, g, h⟩,
  exact ⟨c₁, c₂, h₁, ⟨c₃, c₄, h₂, f, g⟩, h⟩
end

def tensor_map {F₁ G₁ F₂ G₂ : presheaf ct} (f : hom F₁ F₂) (g : hom G₁ G₂) :
  hom (tensor F₁ G₁) (tensor F₂ G₂) :=
λ A a, ⟨a.1, a.2.1, a.2.2.1, f _ a.2.2.2.1, g _ a.2.2.2.2⟩ 

def homp (F G : presheaf ct) : presheaf ct :=
⟨λ c, Σ c₁ c₂ : type cT, term2 ct (c₁.arrow (c₂.arrow c)) → F.1 c → G.1 c,
  sorry⟩

section curry

variables {F G H : presheaf ct}

-- def curryFa (F G H : presheaf ct) : presheaf ct :=
-- ⟨λ A, hom () H, _⟩ 

-- def currya₁ : hom (homp (tensor F G) H) (homp F (homp G H)) :=


def curry {F G H : presheaf ct} : (hom (tensor F G) H) → 
  (hom F (homp G H)) :=
begin
  dsimp [tensor, yoneda, hom, homp] at *,
  exact f _ ⟨x.1, x.2.1, x.2.2, fA, gA⟩
end

end curry

def yoneda_hom (F G : type cT) : yoneda 

def id : presheaf ct := ⟨λ _, unit, λ _ _ _, id⟩

def tensor_id₁ (F : presheaf ct) : hom (tensor F id) F :=
λ A a, a.1

def tensor_id₂ (F : presheaf ct) : hom F (tensor F id) :=
λ A a, (a, ())

def id_tensor₂ (F : presheaf ct) : hom F (tensor id F) :=
λ A a, ((), a)



end presheaf

open category_theory

section

@[derive decidable_eq] inductive type3 (cT : Type) : Type
| const : cT → type3
| arrow : type3 → type3 → type3
| id {} : type3
| tensor : type3 → type3 → type3

def type3.of_type : type cT → type3 cT 
| (type.const T) := type3.const T
| (type.arrow T₁ T₂) := type3.arrow (type3.of_type T₁) (type3.of_type T₂)

def contexti : context cT → type3 cT
| []       := type3.id
| (T :: l) := type3.tensor (type3.of_type T.2) (contexti l)

inductive term3 (const_term : type cT → Type) : Π (A : type3 cT), Type
| const {T : type cT} (t : const_term T) : term3 (type3.of_type T)
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

namespace term3 

variables {const_term : type cT → Type}

def tensor_mk {T₁ T₂ : type3 cT} : term3 const_term (T₁.arrow (T₂.arrow (T₁.tensor T₂))) := 
term3.app term3.curry (term3.id _)

def rid₁ {T : type3 cT} : term3 const_term ((T.tensor type3.id).arrow T) :=
term3.app (term3.comp term3.tensor_symm) term3.lid₁

def rid₂ (T : type3 cT) : term3 const_term (T.arrow (T.tensor type3.id)) :=
term3.app (term3.comp term3.lid₂) term3.tensor_symm

def lift {T : type3 cT} : term3 const_term (T.arrow (type3.id.arrow T)) :=
term3.app term3.curry term3.rid₁

def drop {T : type3 cT} : term3 const_term ((type3.id.arrow T).arrow T) :=
term3.app (term3.comp (term3.rid₂ _)) 
  (term3.app (term3.uncurry) (term3.id _))

def assoc₁ {T₁ T₂ T₃ : type3 cT} : 
  term3 const_term (((T₁.tensor T₂).tensor T₃).arrow (T₁.tensor (T₂.tensor T₃))) :=
term3.app term3.uncurry $ term3.app term3.uncurry $
  term3.app (term3.comp term3.tensor_mk) term3.curry

def assoc₂ {T₁ T₂ T₃ : type3 cT} :
  term3 const_term ((T₁.tensor (T₂.tensor T₃)).arrow ((T₁.tensor T₂).tensor T₃)) :=
term3.app term3.uncurry $ term3.app (term3.comp 
  (term3.app term3.curry tensor_mk)) term3.uncurry

def contexti_append₁ : Π (Γ₁ Γ₂ : context cT), term3 const_term 
  ((contexti (Γ₁ ++ Γ₂)).arrow ((contexti Γ₁).tensor (contexti Γ₂)))
| []      Γ₂ := lid₂
| (T::Γ₁) Γ₂ := term3.app (term3.comp (term3.tensor_map (term3.id _) 
  (contexti_append₁ _ _))) term3.assoc₂
 
def contexti_append₂ : Π (Γ₁ Γ₂ : context cT), term3 const_term 
  (((contexti Γ₁).tensor (contexti Γ₂)).arrow (contexti (Γ₁ ++ Γ₂)))
| []      Γ₂ := lid₁
| (T::Γ₁) Γ₂ := term3.app (term3.comp term3.assoc₁) 
  (term3.tensor_map (term3.id _) (contexti_append₂ _ _))

end term3

variables {const_term : type cT → Type}
variables (const_termi : Π {T : type cT}, const_term T → type3 cT)

def termi : Π {Γ : context cT} {A : type cT} (t : term const_term Γ A),
  term3 const_term ((contexti Γ).arrow (type3.of_type A))
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

inductive term₃ (const_term : type cT → Type) : Π (A : type cT), Type
| const {T : type cT} (t : const_term T) : term₃ T
| id (T : type cT) : term₃ (T.arrow T)
| app {T₁ T₂ : type cT} (f : term₃ (T₁.arrow T₂)) (x : term₃ T₁) : term₃ T₂
| comp {T₁ T₂ T₃ : type cT} (f : term₃ (T₁.arrow T₂)) : 
  term₃ ((T₂.arrow T₃).arrow (T₁.arrow T₃))

end

open term

def const_term : type unit → Type
| (type.arrow (type.const ()) (type.arrow (type.const ()) (type.const ()))) := unit
| _ := empty

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
  app [("a", T), ("b", T)] [("c", T)] 
  (app [] [("a", T), ("b", T)] (const mult) 
    (app [("a", T)] [("b", T)] 
      (app [] [("a", T)] (const mult) (var "a" (type.const ()))) 
        (var "b" (type.const ()))) : _) 
    (var "c" (type.const ()))

example (p q r : M) : 
  termi (@cTi R _ M) (@const_termi _ _ _ op) exmpl₁ = 0 :=
begin
  dunfold exmpl₁,
  simp[termi],
  dsimp [typei, contexti, contexti_append, cTi, const_termi],
  ext,
  simp,

end


