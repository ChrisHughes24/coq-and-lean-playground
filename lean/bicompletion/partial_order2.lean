import order.complete_lattice
import set_theory.ordinal

universes u v

variables (A : Type u) (B : Type v) [partial_order A] [partial_order B]

/-- Aiming to construct a pscompletion of `B` that preserves all sups in `A`.
  So if we have a partial order `C` a monotone function `B -> C` and a `sup_hom`
  from `A -> C` that commute with `f` there is a unique cocontinuous map from
  the pscompletion to `C` such that everything commutes. -/

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

lemma eq_supr (a : presheaf B) : a = ⨆ (p : B) (h : a p), yoneda p :=
begin
  apply le_antisymm; simp only [le_supr_iff, supr_le_iff, yoneda_le_iff],
  { intros B hB p,
    exact hB p },
  { exact λ _, id }
end

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

lemma coyoneda_mono {a b : B} : coyoneda a ≤ coyoneda b ↔ a ≤ b :=
begin
  rw le_coyoneda_iff, refl
end

lemma eq_infi (a : copresheaf B) : a = ⨅ (p : B) (h : a p), coyoneda p :=
begin
  apply le_antisymm; simp only [le_infi_iff, infi_le_iff, le_coyoneda_iff],
  { exact λ _, id },
  { intros B hB p,
    exact hB p },
end

end copresheaf

open presheaf copresheaf

variables (f : A →o B) (hf : ∀ b, ∃ s : set A, is_glb (f '' s) b)

namespace presheaf

def u (a : presheaf B) : copresheaf B :=
⟨λ p, coyoneda a (yoneda p), λ a b hab h x hxA, le_trans (h _ hxA) hab⟩

lemma u_mono : monotone (@u B _):=
λ A B h p hp q hAq, hp _ (h _ hAq)

def d (a : copresheaf B) : presheaf B :=
⟨λ q, ∀ (x : A), a (f x) → q ≤ f x, λ a b hab h x hxA, le_trans hab (h _ hxA)⟩

lemma d_mono : monotone (d f) :=
λ A B h p hp q hAq, hp _ (h _ hAq)

include hf

def gc : galois_connection u (d f) :=
begin
  intros a b,
  dsimp [presheaf.u, presheaf.d],
  split,
  { intros h x hxA y hyB,
    dsimp [copresheaf.le_def] at h,
    apply h,
    assumption,
    assumption },
  { intros h x hxA y hyB,
    dsimp [presheaf.le_def] at *,
    dsimp [yoneda],
    cases hf x with s hs,
    rw [le_is_glb_iff hs, mem_lower_bounds],
    intros z hz,
    rcases hz with ⟨z, hz, rfl⟩,
    apply h,
    assumption,
    rw [← le_coyoneda_iff] at *,
    refine le_trans hxA _,
    refine coyoneda_mono.2 _,
    exact hs.1 (set.mem_image_of_mem _ hz) }
end

open copresheaf

lemma le_d_u (a : presheaf B) : a ≤ d f (u a) := (gc f hf).le_u_l a

@[simp] lemma u_d_u (a : presheaf B) : u (d f (u a)) = u a :=
(gc f hf).l_u_l_eq_l a

@[simp] lemma u_yoneda (p : B) : u (yoneda p) = coyoneda p :=
begin
  rw [u],
  conv_lhs { dsimp [coyoneda] },
  simp only [yoneda_le_iff],
  refl
end

end presheaf

namespace copresheaf

open presheaf

lemma u_d_le (a : copresheaf B) : u (d f a) ≤ a := (gc f hf).l_u_le a

@[simp] lemma d_u_d (a : copresheaf B) : d f (u (d f a)) = d f a :=
(gc f hf).u_l_u_eq_u _

include hf

@[simp] lemma d_coyoneda (p : B) : d f (coyoneda p) = yoneda p :=
begin
  rw [d],
  ext,
  dsimp,
  split,
  { intros h,
    dsimp [yoneda],
    cases hf p with s hs,
    rw [le_is_glb_iff hs, mem_lower_bounds],
    simp only [set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
    intros a ha,
    apply h,
    apply hs.1,
    exact set.mem_image_of_mem _ ha  },
  { intros h y py,
    exact le_trans h py }
end 

end copresheaf

open presheaf copresheaf

variable {B}
include hf
structure pscompletion : Type v :=
( to_presheaf : presheaf B )
( fixed : d f (u to_presheaf) = to_presheaf )

namespace pscompletion

variables {B}

def _root_.presheaf.to_pscompletion (a : presheaf B) : 
  pscompletion f hf :=
⟨d f (u a), by simp *⟩

instance : partial_order (pscompletion f hf) :=
partial_order.lift pscompletion.to_presheaf 
  begin
    rintros ⟨_, _⟩ ⟨_, _⟩,
    simp
  end

lemma le_def {a b : pscompletion f hf} : a ≤ b ↔ a.to_presheaf ≤ b.to_presheaf := iff.rfl

def gi : galois_insertion (_root_.presheaf.to_pscompletion f hf) pscompletion.to_presheaf :=
galois_connection.to_galois_insertion 
  begin
    intros x y,
    simp only [_root_.presheaf.to_pscompletion, le_def],
    rw [← y.fixed, ← (gc f hf).le_iff_le, u_d_u f hf, (gc f hf).le_iff_le],
  end
  (by simp [_root_.presheaf.to_pscompletion, le_def, le_d_u f hf])

instance : complete_lattice (pscompletion f hf) :=
galois_insertion.lift_complete_lattice (gi f hf)

def of_partial_order (a : B) : pscompletion f hf :=
⟨yoneda a, by rw [u_yoneda f hf, d_coyoneda f hf]⟩

end pscompletion