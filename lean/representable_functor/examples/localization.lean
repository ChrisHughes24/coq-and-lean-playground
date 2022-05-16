import tactic
import group_theory.subgroup.basic

variables {M : Type} [comm_monoid M] (a b : submonoid M)

include a

constant localization : Type

omit a

namespace localization

@[instance] protected constant comm_monoid : comm_monoid (localization a)

constant of : M →* localization a

constant is_unit_of (x : M) (hx : x ∈ a) : is_unit (of a x)

variables {N : Type} [comm_monoid N]

constant desc (f : M →* N) (hf : ∀ x ∈ a, is_unit (f x)) : localization a →* N 

@[simp] constant desc_comp_of (f : M →* N) (hf : ∀ x ∈ a, is_unit (f x)) :
  (desc a f hf).comp (of a) = f

@[simp] constant desc_of (f : M →* N) (hf : ∀ x ∈ a, is_unit (f x)) (x : M):
  desc a f hf (of a x) = f x

@[ext] constant hom_ext {f g : localization a →* N}
  (h : f.comp (of a) = g.comp (of a)) : f = g 

end localization

open localization

noncomputable def iso : localization (b.map (of a)) ≃* localization (a ⊔ b) :=
monoid_hom.to_mul_equiv 
  (desc _ (desc _ (of (a ⊔ b)) 
    (λ x hx, is_unit_of _ _ (submonoid.mem_sup_left hx))) 
    (λ x hx, begin
      rw [submonoid.mem_map] at hx,
      rcases hx with ⟨y, hy, rfl⟩,
      rw [desc_of],
      exact is_unit_of _ _ (submonoid.mem_sup_right hy)  
    end))
  (desc _ ((of _).comp (of _)) 
    (λ x hx, begin
      rw [submonoid.mem_sup] at hx,
      rcases hx with ⟨y, hy, z, hz, rfl⟩,
      rw [map_mul],
      refine is_unit.mul _ _,
      { rw [monoid_hom.comp_apply],
        refine is_unit.map _ (is_unit_of _ _ hy), },
      { refine is_unit_of _ _ (submonoid.mem_map_of_mem _ hz) }
    end))
  (by ext; simp)
  (by ext; simp)

lemma iso_commutes : (iso a b).to_monoid_hom.comp ((of (b.map (of a))).comp (of a)) = of (a ⊔ b) :=
by ext; simp [iso]
