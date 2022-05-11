import tactic
import group_theory.semidirect_product
import data.int.cast
import group_theory.eckmann_hilton

noncomputable theory

constant klein_bottle : Type

@[instance] protected constant 
  klein_bottle.group : group klein_bottle

namespace klein_bottle

variables {α G : Type} [group G] 

constant a : klein_bottle

constant b : klein_bottle

constant extend (Xa : G) (Xb : G)
  (h : Xa * Xb * Xa * Xb⁻¹ = 1)  : klein_bottle →* G

@[simp] constant extend_a (Xa : G) (Xb : G)
  (h : Xa * Xb * Xa * Xb⁻¹ = 1) : extend Xa Xb h a = Xa

@[simp] constant extend_b (Xa : G) (Xb : G)
  (h : Xa * Xb * Xa * Xb⁻¹ = 1) : extend Xa Xb h b = Xb

constant hom_ext {f g : klein_bottle →* G} 
  (h1 : f a = g a) (h2 : f b = g b) : f = g

end klein_bottle

constant Cinfinity : Type

@[instance] protected constant Cinfinity.comm_group : comm_group Cinfinity

namespace Cinfinity

variables {α G : Type} [group G] 

constant X : Cinfinity

constant extend (x : G) : Cinfinity →* G

@[simp] constant extend_X (x : G) : extend x X = x

@[ext] constant hom_ext {f g : Cinfinity →* G} (h : f X = g X) : f = g

end Cinfinity

def action : Cinfinity →* mul_aut Cinfinity :=
Cinfinity.extend ⟨has_inv.inv, has_inv.inv, inv_inv, inv_inv, by simp [mul_comm]⟩

example : klein_bottle ≃* Cinfinity ⋊[action] Cinfinity :=
monoid_hom.to_mul_equiv 
  (klein_bottle.extend 
    (semidirect_product.inl Cinfinity.X) 
    (semidirect_product.inr Cinfinity.X) 
    begin
      rw [mul_assoc, mul_assoc, ← mul_assoc _ _ (_⁻¹), ← map_inv, ← semidirect_product.inl_aut],
      simp [action],
    end) 
  (semidirect_product.lift 
    (Cinfinity.extend klein_bottle.a) 
    (Cinfinity.extend klein_bottle.b)
    (λ g, begin
      dsimp [action],
      simp,
      
    end))
  _ 
  _