import data.vector
import data.equiv.denumerable
import data.list.sort
import ring_theory.tensor_product
import algebra.category.Module.basic

@[derive decidable_eq] inductive type (cT : Type) : Type
| const : cT → type
| arrow : type → type → type
| tensor : type → type → type

variables (cT : Type)

@[reducible] def context (cT : Type) : Type := list (string × type cT)

-- instance : has_append (context cT) :=
-- ⟨λ a b : list (string × type cT), list.append a b⟩

-- instance : has_scalar (string × type cT) (context cT) :=
-- ⟨list.cons⟩

variables {cT}

inductive term (const_term : type cT → Type) : Π (Γ : context cT) (A : type cT), Type
| const {T : type cT} (t : const_term T) : term [] T
| var (a : string) (T : type cT) : term [(a, T)] T
| app (Γ₁ Γ₂ : context cT) {T₁ T₂ : type cT} (f : term Γ₁ (T₁.arrow T₂)) (x : term Γ₂ T₁) : 
    term (Γ₁ ++ Γ₂) T₂
| lambda {Γ : context cT} (a : string) (T₁ : type cT) {T₂ : type cT}
    (t : term (Γ ++ [(a, T₁)]) T₂) : term Γ (T₁.arrow T₂)

open category_theory

variables {R : Type} [comm_ring R] 

section

variables (cTi : cT → Module.{0 0} R) 

open_locale tensor_product

def typei : type cT → Module R
| (type.const T)     := cTi T
| (type.arrow T₁ T₂) := Module.of R (typei T₁ →ₗ[R] typei T₂)
| (type.tensor T₁ T₂) := Module.of R (typei T₁ ⊗[R] typei T₂)

def contexti : context cT → Module R
| []       := Module.of R R
| (T :: l) := Module.of R (typei cTi T.2 ⊗[R] contexti l)

def contexti_append : Π (Γ₁ Γ₂ : context cT), 
  (contexti cTi (Γ₁ ++ Γ₂)) ≃ₗ[R] contexti cTi Γ₁ ⊗[R] contexti cTi Γ₂
| []      Γ₂ := (tensor_product.lid R (contexti cTi Γ₂)).symm
| (A::Γ₁) Γ₂ := (tensor_product.congr  (linear_equiv.refl R (typei cTi A.2))
    (contexti_append Γ₁ Γ₂)).trans 
  (tensor_product.assoc R _ _ _).symm

variables {const_term : type cT → Type}
variables (const_termi : Π {T : type cT}, const_term T → typei cTi T)

def termi : Π {Γ : context cT} {A : type cT} (t : term const_term Γ A),
  contexti cTi Γ →ₗ[R] typei cTi A
| _ A (term.const t) := linear_map.to_span_singleton _ _ (const_termi t)
| _ _ (term.var _ A) := (tensor_product.rid _ _).to_linear_map
| _ T₂ (@term.app  _ _ Γ₁ Γ₂ T₁ _ f x) := 
  linear_map.comp (tensor_product.uncurry R (contexti cTi Γ₁) (contexti cTi Γ₂) _
       (linear_map.comp (linear_map.lcomp R _ (termi x)) (termi f)))
     (contexti_append _ Γ₁ Γ₂).to_linear_map
| Γ (type.arrow _ T₂) (term.lambda a T₁ t) := begin
  refine tensor_product.curry _,
  have h₂ := (contexti_append cTi Γ [(a, T₁)]).trans
    (tensor_product.congr (linear_equiv.refl R (contexti cTi Γ)) 
      (tensor_product.rid _ _)),
  refine linear_map.comp (termi t) h₂.symm.to_linear_map,
end
using_well_founded { dec_tac :=`[exact sorry] }

end

variables {M : Module.{0 0} R} (op : M →ₗ[R] M →ₗ[R] M)

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


