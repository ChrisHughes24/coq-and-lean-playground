import tactic
import group_theory.semidirect_product
import data.int.cast
import group_theory.eckmann_hilton

noncomputable theory

constant free_group (α : Type) : Type

@[instance] protected constant free_group.group (α : Type) : group (free_group α)

namespace free_group

variables {α G : Type} [group G] 

constant X : α → free_group α

constant extend (f : α → G) : free_group α →* G

constant extend_X (f : α → G) : extend f ∘ X = f
constant extend_X' (f : α → G) (a : α) : 
  extend f (X a) = f a

constant hom_ext {f g : free_group α →* G} 
  (h : f ∘ X = g ∘ X) : f = g

end free_group

lemma bool.hom_ext {α : Type} {f g : bool → α}
  (h1 : f tt = g tt) (h2 : f ff = g ff) : f = g :=
by ext x; cases x; assumption
  

def action : free_group unit →* mul_aut (free_group (free_group unit)) :=
free_group.extend (λ x, monoid_hom.to_mul_equiv 
  (free_group.extend (λ n, free_group.X (n * free_group.X ()))) 
  (free_group.extend (λ n, free_group.X (n / free_group.X ())))  
  (free_group.hom_ext 
    begin
      funext n,
      rw [monoid_hom.coe_comp, function.comp.assoc, free_group.extend_X,
        function.comp_apply, free_group.extend_X', function.comp_apply,
        monoid_hom.id_apply, mul_div_cancel''],
    end)
  (free_group.hom_ext 
    begin
      funext n,
      rw [monoid_hom.coe_comp, function.comp.assoc, free_group.extend_X,
        function.comp_apply, free_group.extend_X', function.comp_apply,
        monoid_hom.id_apply, div_mul_cancel'],
    end))

example : free_group bool ≃* free_group (free_group unit) ⋊[action] free_group unit :=
monoid_hom.to_mul_equiv 
  (free_group.extend (λ b, cond b 
    (semidirect_product.inl (free_group.X 1)) 
    (semidirect_product.inr (free_group.X ())))) 
  (semidirect_product.lift 
    (free_group.extend (free_group.extend (λ _, mul_aut.conj (free_group.X ff) (free_group.X tt)))) 
    (free_group.extend (λ _, free_group.X ff)) 
    (λ g, begin
      refine free_group.hom_ext _,
      simp [action],
      ext,
      simp [free_group.extend_X'],
      
    end)) 
  (free_group.hom_ext $ bool.hom_ext 
    begin
      rw [monoid_hom.coe_comp, function.comp.assoc, 
        free_group.extend_X, function.comp_app, bool.cond_tt,
        semidirect_product.lift_inl,
        free_group.extend_X', function.comp_app, monoid_hom.id_apply],
        rw [zpow_zero, monoid_hom.map_one, mul_aut.one_apply],
    end 
    begin
      rw [monoid_hom.coe_comp, function.comp.assoc, 
        free_group.extend_X, function.comp_app, bool.cond_ff,
        semidirect_product.lift_inr,
        free_group.extend_X', function.comp_app, monoid_hom.id_apply],
    end)
  (semidirect_product.hom_ext 
    (free_group.hom_ext begin
      funext x,
      rw [monoid_hom.comp_assoc, semidirect_product.lift_comp_inl,
        monoid_hom.coe_comp, function.comp.assoc, free_group.extend_X,
        monoid_hom.id_comp, function.comp_apply],
      rw [mul_aut.conj_apply, monoid_hom.map_mul, monoid_hom.map_mul,
        monoid_hom.map_inv, monoid_hom.map_zpow, free_group.extend_X',
        bool.cond_ff, free_group.extend_X', bool.cond_tt, 
        ← monoid_hom.map_zpow, ← monoid_hom.map_inv,
        ← semidirect_product.inl_aut, action, monoid_hom.map_zpow, 
        free_group.extend_X', function.comp_apply],
      refine congr_arg _ _,
      conv_rhs { rw [← add_zero x] },
      generalize h0 : (0 : ℤ) = n,
      clear h0,
      revert n,
      refine int.induction_on x _ _ _,
      { simp, },
      { simp [zpow_add, free_group.extend_X', add_assoc, add_comm, add_left_comm,
        monoid_hom.to_mul_equiv_apply] {contextual := tt} },
      { simp [zpow_add, free_group.extend_X', add_assoc, add_comm, add_left_comm,
        monoid_hom.to_mul_equiv_apply] {contextual := tt} }
    end)
    (free_group.hom_ext begin
      funext x,
      cases x,
      simp [free_group.extend_X']
    end))