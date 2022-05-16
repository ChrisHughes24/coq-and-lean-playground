import tactic
import group_theory.congruence

namespace units

variables {M : Type} [monoid M]

def of : units M →* M := 
⟨coe, rfl, λ _ _, rfl⟩

variables {G : Type} [group G] (f : G →* M)

def restrict : G →* units M :=
⟨λ x, ⟨f x, f x⁻¹, 
  by rw [← map_mul, _root_.mul_inv_self, map_one], 
  by rw [← map_mul, _root_.inv_mul_self, map_one]⟩, 
  by ext; simp, λ _ _, by ext; simp⟩

@[simp] lemma of_comp_restrict : of.comp (restrict f) = f :=
by ext; refl

@[simp] lemma of_restrict (x : G) : of (restrict f x) = f x := rfl

@[ext] lemma hom_ext {f g : G →* units M} (h : of.comp f = of.comp g) : f = g :=
begin
  ext x,
  exact monoid_hom.congr_fun h x
end

end units

@[derive monoid] def abelianization (M : Type) [monoid M] : Type :=
con.quotient (con_gen (λ a b : M, ∃ x y : M, a = x * y ∧ b = y * x))

namespace abelianization

variables {M : Type} [monoid M]

instance : comm_monoid (abelianization M) :=
{ mul_comm := λ a b, begin
    dsimp [abelianization] at *,
    refine con.induction_on₂ a b (λ a b, _),
    rw [← con.coe_mul, ← con.coe_mul, con.eq],
    refine con_gen.rel.of _ _ _,
    use [a, b],
    simp
  end,
  ..show monoid (abelianization M), by apply_instance }

def of : M →* abelianization M :=
by dsimp [abelianization]; exact
{ to_fun := coe,
  map_mul' := by simp,
  map_one' := by simp }


instance {G : Type} [group G] : comm_group (abelianization G) :=
{ inv := λ x, con.lift_on x (λ x, of (x⁻¹)) begin
    intros a b h, dsimp,
    induction h with x y h,
    { rcases h with ⟨x, y, rfl, rfl⟩,
      simp [mul_comm] },
    { refl },
    { simp * },
    { cc },
    { simp * }
  end,
  mul_left_inv := λ a, begin
    dsimp [abelianization, of] at *,
    refine con.induction_on a (λ a, _),
    simp
  end,
  ..show comm_monoid (abelianization G), by apply_instance }

variables {N : Type} [comm_monoid N] (f : M →* N)

def desc : abelianization M →* N :=
con.lift _ f (con.con_gen_le begin
    rintros _ _ ⟨a, b, rfl, rfl⟩,
    show f (a * b) = f (b * a),
    simp [mul_comm]
  end)

@[simp] lemma desc_comp_of : (desc f).comp of = f :=
begin
  ext,
  refl
end

@[simp] lemma desc_of (x : M) : desc f (of x) = f x := rfl

@[ext] lemma hom_ext {f g : abelianization M →* N} 
  (h : f.comp of = g.comp of) : f = g :=
begin
  ext x,
  refine con.induction_on x (λ x, _),
  convert monoid_hom.congr_fun h x
end 

end abelianization

variables {G M : Type} [group G] [comm_monoid M] (f : G →* M)

example : abelianization.desc (units.restrict f) = 
  units.restrict (abelianization.desc f) := 
begin
  ext; simp,

end