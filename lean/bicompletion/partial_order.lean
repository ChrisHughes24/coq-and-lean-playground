import order.complete_lattice
import set_theory.ordinal

universes u v

variables (A : Type u) (B : Type v) [partial_order A] [partial_order B]

structure sup_hom : Type (max u v) :=
(to_fun : A → B)
(monotone : monotone to_fun)
(sup : ∀ (s : set A) (a : A), is_lub s a → is_lub (to_fun '' s) (to_fun a))

/-- Aiming to construct a cocompletion of `B` that preserves all sups in `A`.
  So if we have a partial order `C` a monotone function `B -> C` and a `sup_hom`
  from `A -> C` that commute with `f` there is a unique cocontinuous map from
  the cocompletion to `C` such that everything commutes. -/

def presheaf : Type* :=
{ s : B → Prop // ∀ a b, a ≤ b → s b → s a }

variables {A B}

namespace presheaf

instance : has_coe_to_fun (presheaf B) (λ _, B → Prop) :=
⟨subtype.val⟩

@[simp] lemma coe_mk (s : B → Prop) (hs : ∀ a b, a ≤ b → s b → s a) :
  @coe_fn (presheaf B) _ _ (⟨s, hs⟩ : presheaf B) = s := rfl

instance : partial_order (presheaf B) :=
{ le := λ a b, ∀ x, a x → b x,
  le_trans := λ a b c hab hbc x hax, hbc _ (hab _ hax),
  le_refl := λ _ _, id,
  le_antisymm := λ a b hab hba, subtype.val_injective (funext $ λ x, propext ⟨hab _, hba _⟩) }

lemma le_def {a b : presheaf B} : a ≤ b = ∀ x, a x → b x := rfl

instance : has_Inf (presheaf B) :=
{ Inf := λ s, ⟨λ p, ∀ B : presheaf B, B ∈ s → B p, 
     λ a b hab h B hBs, B.2 _ _ hab (h _ hBs)⟩ }

instance : complete_lattice (presheaf B) :=
complete_lattice_of_Inf _
  (λ s, begin
    split,
    { dsimp [Inf, lower_bounds],
      intros B hBs p h,
      apply h,
      exact hBs },
    { dsimp [Inf, upper_bounds, lower_bounds],
      intros B h p hBp B hBs,
      apply h,
      exact hBs,
      exact hBp }
  end)

lemma infi_def {ι : Sort*} (a : ι → presheaf B) : 
  infi a = ⟨λ p, ∀ i, a i p, λ x y hxy h i, (a i).2 _ y hxy (h i)⟩ :=
le_antisymm 
  (infi_le_iff.2 (λ B h p hBp i, h i _ hBp)) 
  (le_infi (λ i p h, h _))

lemma supr_def {ι : Sort*} (a : ι → presheaf B) : 
  supr a = ⟨λ p, ∃ i, a i p, λ x y hxy ⟨i, hi⟩, ⟨i, (a i).2 x y hxy hi⟩⟩ :=
le_antisymm 
  (supr_le_iff.2 (λ i p h, ⟨i, h⟩)) 
  (le_supr_iff.2 (λ B h p ⟨i, hi⟩, h i _ hi))

def yoneda (a : B) : presheaf B :=
⟨λ b, b ≤ a, λ b c, le_trans⟩

def yoneda_le_iff (a : presheaf B) (p : B) : yoneda p ≤ a ↔ a p :=
begin
  simp [yoneda, presheaf.le_def],
  split,
  { intro h, apply h, exact le_rfl },
  { intros h x hxp,
    apply a.2,
    apply hxp,
    exact h }
end

lemma yoneda_mono {a b : B} : yoneda a ≤ yoneda b ↔ a ≤ b :=
begin
  rw yoneda_le_iff, refl,
end

lemma eq_supr {a : presheaf B} : a = ⨆ (p : B) (h : a p), yoneda p :=
begin
  apply le_antisymm; simp only [le_supr_iff, supr_le_iff, yoneda_le_iff],
  { intros B hB p,
    exact hB p },
  { exact λ _, id }
end

def restrict (f : sup_hom A B) (a : presheaf B) : presheaf A :=
⟨λ x, a.1 (f.1 x), λ x y hxy h, a.2 _ _ (f.monotone hxy) h⟩ 

end presheaf

variable (B)

def copresheaf : Type* :=
{ s : B → Prop // ∀ a b, a ≤ b → s a → s b }

variable {B}

namespace copresheaf

instance : has_coe_to_fun (copresheaf B) (λ _, B → Prop) :=
⟨subtype.val⟩

@[simp] lemma coe_mk (s : B → Prop) (hs : ∀ a b, a ≤ b → s a → s b) :
  @coe_fn (copresheaf B) _ _ (⟨s, hs⟩ : copresheaf B) = s := rfl

instance : partial_order (copresheaf B) :=
{ le := λ a b, ∀ x, b x → a x,
  le_trans := λ a b c hab hbc x hcx, hab _ (hbc _ hcx),
  le_refl := λ _ _, id,
  le_antisymm := λ a b hab hba, subtype.val_injective (funext $ λ x, propext ⟨hba _, hab _⟩) }

lemma le_def {a b : copresheaf B} : a ≤ b = ∀ x, b x → a x := rfl

instance : has_Sup (copresheaf B) :=
{ Sup := λ s, ⟨λ p, ∀ B : copresheaf B, B ∈ s → B p, 
     λ a b hab h B hBs, B.2 _ _ hab (h _ hBs)⟩ }

instance : complete_lattice (copresheaf B) :=
complete_lattice_of_Sup _
  (λ s, begin
    split,
    { dsimp [Sup, upper_bounds],
      intros B hBs p h,
      apply h,
      exact hBs },
    { dsimp [Inf, upper_bounds, lower_bounds],
      intros B h p hBp B hBs,
      apply h,
      exact hBs,
      exact hBp }
  end)

lemma infi_def {ι : Sort*} (a : ι → copresheaf B) : 
  infi a = ⟨λ p, ∃ i, a i p, λ x y hxy ⟨i, hi⟩, ⟨i, (a i).2 x y hxy hi⟩⟩ :=
le_antisymm 
  (infi_le_iff.2 (λ B h p ⟨i, hi⟩, h i _ hi)) 
  (le_infi_iff.2 (λ i p h, ⟨i, h⟩))

lemma supr_def {ι : Sort*} (a : ι → copresheaf B) : 
  supr a = ⟨λ p, ∀ i, a i p, λ x y hxy h i, (a i).2 _ y hxy (h i)⟩ :=
le_antisymm 
  (supr_le_iff.2 (λ i p h, h _)) 
  (le_supr_iff.2 (λ B h p hBp i, h i _ hBp))

def coyoneda (a : B) : copresheaf B :=
⟨λ b, a ≤ b, λ b c, function.swap le_trans⟩

def le_coyoneda_iff (a : copresheaf B) (p : B) : a ≤ coyoneda p ↔ a p :=
begin
  simp [copresheaf.coyoneda, copresheaf.le_def],
  split,
  { intro h, apply h, exact le_rfl },
  { intros h x hxp,
    apply a.2,
    apply hxp,
    exact h }
end

lemma eq_infi {a : copresheaf B} : a = ⨅ (p : B) (h : a p), coyoneda p :=
begin
  apply le_antisymm; simp only [le_infi_iff, infi_le_iff, le_coyoneda_iff],
  { exact λ _, id },
  { intros B hB p,
    exact hB p },
end

end copresheaf

open presheaf copresheaf

namespace presheaf

def u (f : A →o B) (a : presheaf B) : copresheaf B :=
⟨λ p, Π (x : B), a x → x ≤ p, λ a b hab h x hxA, le_trans (h _ hxA) hab⟩

lemma u_mono {f : A →o B} : monotone (u f):=
λ A B h p hp q hAq, hp _ (h _ hAq)

end presheaf

namespace copresheaf

def d (f : A →o B) (a : copresheaf B) : presheaf B :=
⟨λ q, Π (x : A), a (f x) → q ≤ f x, λ a b hab h x hxA, le_trans hab (h _ hxA)⟩

lemma d_mono {f : A →o B} : monotone (d f) :=
λ A B h p hp q hAq, hp _ (h _ hAq)

end copresheaf

def gc {f : A →o B} : galois_connection (presheaf.u f) (copresheaf.d f) :=
begin
  intros A B,
  dsimp [presheaf.u, copresheaf.d],
  split,
  { intros h x hxA y hyB,
    dsimp [copresheaf.le_def] at h,
    apply h,
    assumption,
    assumption,
     },
  { intros h x hxA y hyB,
    dsimp [presheaf.le_def] at *,
    apply h,
    assumption,
    assumption }
end

namespace presheaf

open copresheaf


lemma le_d_u (a : presheaf B) : a ≤ d (u a) := gc.le_u_l a

@[simp] lemma u_d_u (a : presheaf B) : (u (d (u a))) = u a :=
le_antisymm 
  begin
    dsimp [d, u],
    intros p hp,
    dsimp [yoneda, coyoneda, presheaf.le_def] at *,
    intros q h,
    apply h,
    apply hp
  end
  (gc.monotone_l (le_d_u _))


@[simp] lemma u_yoneda (p : B) : u (yoneda p) = coyoneda p :=
begin
  rw [u],
  conv_lhs {dsimp [coyoneda]},
  simp only [yoneda_le_iff],
  refl
end

end presheaf

namespace copresheaf

open presheaf

lemma u_d_le (a : copresheaf B) : u (d a) ≤ a := gc.l_u_le a

@[simp] lemma d_u_d (a : copresheaf B) : d (u (d a)) = d a :=
le_antisymm 
  (gc.monotone_u (u_d_le _))
  begin
    dsimp [d, u],
    intros p hp,
    dsimp [yoneda, coyoneda, presheaf.le_def] at *,
    intros q h,
    apply h,
    apply hp
  end

@[simp] lemma d_coyoneda (p : B) : d (coyoneda p) = yoneda p :=
begin
  rw [d],
  conv_lhs {dsimp only [yoneda]},
  simp only [le_coyoneda_iff],
  refl
end

end copresheaf

open presheaf copresheaf

structure cocompletion (f : sup_hom A B) : Type (max u v) :=
( to_presheaf : presheaf B )
( fixed : d (u (restrict f to_presheaf)) = _ ) 

variables {f : sup_hom A B}

namespace cocompletion

instance : partial_order (cocompletion f) :=
partial_order.lift cocompletion.to_presheaf 
  begin
    rintros ⟨_, _⟩ ⟨_, _⟩,
    simp
  end

lemma le_def {a b : cocompletion f} : a ≤ b ↔ a.to_presheaf ≤ b.to_presheaf := iff.rfl

instance : has_Inf (cocompletion f) :=
⟨λ s, ⟨⨅ (a : cocompletion f) (h : a ∈ s), a.to_presheaf, begin
  dsimp [restrict,u, d, yoneda, coyoneda],
  apply subtype.ext,
  dsimp,
  funext x,
  simp only [presheaf.infi_def],
  simp only [copresheaf.le_def, presheaf.le_def],
  dsimp,
  ext,
  split,
  { intros, }
  
end⟩⟩

end cocompletion