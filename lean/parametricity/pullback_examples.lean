import tactic

class c1 (X : Type) :=
( f : (X → bool) → X )

namespace c1

variables (X Y Z : Type) [c1 X] [c1 Y] [c1 Z]

structure hom : Type :=
( to_fun : X → Y )
( comm : ∀ (s : Y → bool), c1.f s = to_fun (c1.f (s ∘ to_fun)))

instance : has_coe_to_fun (hom X Y) (λ _, X → Y) :=
{ coe := hom.to_fun }

variables {X Y Z}

def pullback (f : hom X Z) (g : hom Y Z) : Type :=
{ x : X × Y // f x.1 = g x.2 }

def relation (s : set (X × Y)) : Prop :=
∀ (f : X → bool) (g : Y → bool), (∀ x y, (x, y) ∈ s → f x = g y) → 
  (c1.f f, c1.f g) ∈ s

def relation_obj (s : set (X × Y)) (hs : relation s) : c1 s :=
{ f := λ i, _ }

-- Don't think possible
instance (f : hom X Z) (g : hom Y Z) : c1 (pullback f g) :=
{ f := λ s, begin
   fsplit,
   split,
   apply c1.f,
   intro x,
   
end  }

end c1