import tactic
import group_theory.subgroup.basic

open subgroup

variables {G : Type} [group G]

namespace pullback

variables {H K : Type} [group H] [group K] 
  (i : H →* G) (j : K →* G) 

def pullback : subgroup (H × K) :=
{ carrier := {x | i x.1 = j x.2},
  one_mem' := by simp,
  mul_mem' := by simp {contextual := tt},
  inv_mem' := by simp {contextual := tt} }

def fst : pullback i j →* H := 
{ to_fun := λ x, x.1.1,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

def snd : pullback i j →* K := 
{ to_fun := λ x, x.1.2,
  map_one' := rfl,
  map_mul' := λ _ _, rfl }

lemma comp_fst_eq_comp_snd : i.comp (fst i j) = j.comp (snd i j) :=
monoid_hom.ext $ λ x, x.2 

def restrict {L : Type} [group L] (f : L →* H) (g : L →* K)
  (hfg : i.comp f = j.comp g) : L →* pullback i j :=
{ to_fun := λ x, ⟨⟨f x, g x⟩, monoid_hom.congr_fun hfg x⟩,
  map_one' := subtype.ext (prod.ext (map_one f) (map_one g)),
  map_mul' := λ a b, subtype.ext (prod.ext (map_mul f _ _) (map_mul g _ _)) }

@[simp] lemma fst_comp_restrict {L : Type} [group L] (f : L →* H) (g : L →* K)
  (hfg : i.comp f = j.comp g) : 
  (fst i j).comp (restrict i j f g hfg) = f :=
monoid_hom.ext (λ _, rfl)

@[simp] lemma snd_comp_restrict {L : Type} [group L] (f : L →* H) (g : L →* K)
  (hfg : i.comp f = j.comp g) : 
  (snd i j).comp (restrict i j f g hfg) = g :=
monoid_hom.ext (λ _, rfl)

@[simp] lemma fst_restrict {L : Type} [group L] (f : L →* H) (g : L →* K)
  (hfg : i.comp f = j.comp g) (x : L) : 
  fst i j (restrict i j f g hfg x) = f x :=
rfl

@[simp] lemma snd_restrict {L : Type} [group L] (f : L →* H) (g : L →* K)
  (hfg : i.comp f = j.comp g) (x : L) : 
  snd i j (restrict i j f g hfg x) = g x :=
rfl

@[ext] lemma hom_ext {L : Type} [group L] {f g : L →* pullback i j}
  (h1 : (fst i j).comp f = (fst i j).comp g)
  (h2 : (snd i j).comp f = (snd i j).comp g) :
  f = g :=
monoid_hom.ext (λ x, subtype.ext (prod.ext 
  (monoid_hom.congr_fun h1 x) 
  (monoid_hom.congr_fun h2 x)))

end pullback
