import order.galois_connection
import data.set_like.basic

variables (P : Type) [partial_order P]

def presheaf : Type :=
{ s : P → Prop // ∀ a b, a ≤ b → s b → s a }

variable {P}

namespace presheaf

instance : has_coe_to_fun (presheaf P) (λ _, P → Prop) :=
⟨subtype.val⟩

@[simp] lemma coe_mk (s : P → Prop) (hs : ∀ a b, a ≤ b → s b → s a) :
  @coe_fn (presheaf P) _ _ (⟨s, hs⟩ : presheaf P) = s := rfl

instance : partial_order (presheaf P) :=
{ le := λ A B, ∀ x, A x → B x,
  le_trans := λ A B C hAB hBC x hAx, hBC _ (hAB _ hAx),
  le_refl := λ A x, id,
  le_antisymm := λ A B hAB hBA, subtype.val_injective (funext $ λ x, propext ⟨hAB _, hBA _⟩) }

lemma le_def {A B : presheaf P} : A ≤ B = ∀ x, A x → B x := rfl

instance : has_Inf (presheaf P) :=
{ Inf := λ s, ⟨λ p, ∀ A : presheaf P, A ∈ s → A p, 
     λ a b hab h A hAs, A.2 _ _ hab (h _ hAs)⟩ }

instance : complete_lattice (presheaf P) :=
complete_lattice_of_Inf _
  (λ s, begin
    split,
    { dsimp [Inf, lower_bounds],
      intros A hAs p h,
      apply h,
      exact hAs },
    { dsimp [Inf, upper_bounds, lower_bounds],
      intros A h p hAp B hBs,
      apply h,
      exact hBs,
      exact hAp }
  end)

lemma infi_def {ι : Sort*} (A : ι → presheaf P) : 
  infi A = ⟨λ p, ∀ i, A i p, λ x y hxy h i, (A i).2 _ y hxy (h i)⟩ :=
le_antisymm 
  (infi_le_iff.2 (λ B h p hBp i, h i _ hBp)) 
  (le_infi (λ i p h, h _))

lemma supr_def {ι : Sort*} (A : ι → presheaf P) : 
  supr A = ⟨λ p, ∃ i, A i p, λ x y hxy ⟨i, hi⟩, ⟨i, (A i).2 x y hxy hi⟩⟩ :=
le_antisymm 
  (supr_le_iff.2 (λ i p h, ⟨i, h⟩)) 
  (le_supr_iff.2 (λ B h p ⟨i, hi⟩, h i _ hi))

end presheaf

def yoneda (a : P) : presheaf P :=
⟨λ b, b ≤ a, λ b c, le_trans⟩

def yoneda_le_iff (A : presheaf P) (p : P) : yoneda p ≤ A ↔ A p :=
begin
  simp [yoneda, presheaf.le_def],
  split,
  { intro h, apply h, exact le_rfl },
  { intros h x hxp,
    apply A.2,
    apply hxp,
    exact h }
end

lemma yoneda_mono {a b : P} : yoneda a ≤ yoneda b ↔ a ≤ b :=
begin
  rw yoneda_le_iff, refl,
end

lemma presheaf.eq_supr {A : presheaf P} : A = ⨆ (p : P) (h : A p), yoneda p :=
begin
  apply le_antisymm; simp only [le_supr_iff, supr_le_iff, yoneda_le_iff],
  { intros B hB p,
    exact hB p },
  { exact λ _, id }
end

variable (P)

def copresheaf : Type := 
{ s : set P // ∀ a b, a ≤ b → s a → s b }

variable {P}

namespace copresheaf

instance : has_coe_to_fun (copresheaf P) (λ _, P → Prop) :=
⟨subtype.val⟩

@[simp] lemma coe_mk (s : P → Prop) (hs : ∀ a b, a ≤ b → s a → s b) :
  @coe_fn (copresheaf P) _ _ (⟨s, hs⟩ : copresheaf P) = s := rfl

instance : partial_order (copresheaf P) :=
{ le := λ A B, ∀ x, B x → A x,
  le_trans := λ A B C hAB hBC x hAx, hAB _ (hBC _ hAx),
  le_refl := λ A x, id,
  le_antisymm := λ A B hAB hBA, subtype.val_injective (funext $ λ x, propext ⟨hBA _, hAB _⟩) }

instance : has_Sup (copresheaf P) :=
{ Sup := λ s, ⟨λ p, ∀ A : copresheaf P, A ∈ s → A p, 
     λ a b hab h A hAs, A.2 _ _ hab (h _ hAs)⟩ }

instance : complete_lattice (copresheaf P) :=
complete_lattice_of_Sup _ 
  (λ s, begin
    split,
    { dsimp [Sup, upper_bounds],
      intros A hAs p h,
      apply h,
      exact hAs },
    { dsimp [Inf, upper_bounds, lower_bounds],
      intros A h p hAp B hBs,
      apply h,
      exact hBs,
      exact hAp }
  end)

lemma infi_def {ι : Sort*} (A : ι → copresheaf P) : 
  infi A = ⟨λ p, ∃ i, A i p, λ x y hxy ⟨i, hi⟩, ⟨i, (A i).2 x y hxy hi⟩⟩ :=
le_antisymm 
  (infi_le_iff.2 (λ B h p ⟨i, hi⟩, h i _ hi)) 
  (le_infi_iff.2 (λ i p h, ⟨i, h⟩))

lemma supr_def {ι : Sort*} (A : ι → copresheaf P) : 
  supr A = ⟨λ p, ∀ i, A i p, λ x y hxy h i, (A i).2 _ y hxy (h i)⟩ :=
le_antisymm 
  (supr_le_iff.2 (λ i p h, h _)) 
  (le_supr_iff.2 (λ B h p hBp i, h i _ hBp))

lemma le_def {A B : copresheaf P} : A ≤ B = ∀ x, B x → A x := rfl

end copresheaf

def coyoneda (a : P) : copresheaf P :=
⟨λ b, a ≤ b, λ b c, function.swap le_trans⟩

def le_coyoneda_iff (A : copresheaf P) (p : P) : A ≤ coyoneda p ↔ A p :=
begin
  simp [yoneda, copresheaf.le_def],
  split,
  { intro h, apply h, exact le_rfl },
  { intros h x hxp,
    apply A.2,
    apply hxp,
    exact h }
end

lemma copresheaf.eq_infi {A : copresheaf P} : A = ⨅ (p : P) (h : A p), coyoneda p :=
begin
  apply le_antisymm; simp only [le_infi_iff, infi_le_iff, le_coyoneda_iff],
  { exact λ _, id },
  { intros B hB p,
    exact hB p },
end

lemma is_glb_yoneda {x : P} : is_glb {y | coyoneda (yoneda x) y} (yoneda x) :=
begin
  split,
  { dsimp [lower_bounds, yoneda, coyoneda],
    exact λ _, id },
  { dsimp [upper_bounds, lower_bounds, yoneda, coyoneda],
    intros A h y hAy,
    exact @h (yoneda x) (λ _, id) y hAy }
end

lemma is_lub_coyoneda {x : P} : is_lub {y | yoneda (coyoneda x) y} (coyoneda x) :=
begin
  split,
  { dsimp [lower_bounds, yoneda, coyoneda],
    exact λ _, id },
  { dsimp [upper_bounds, lower_bounds, yoneda, coyoneda],
    intros A h y hAy,
    exact @h (coyoneda x) (λ _, id) y hAy }
end

def u (A : presheaf P) : copresheaf P :=
⟨λ p, coyoneda A (yoneda p), λ a b hab h x hxA, le_trans (h _ hxA) hab⟩

lemma u_mono : monotone (@u P _) :=
λ A B h p hp q hAq, hp _ (h _ hAq)

def d (B : copresheaf P) : presheaf P :=
⟨λ q, yoneda B (coyoneda q), λ a b hab h x hxA, le_trans hab (h _ hxA)⟩

lemma d_mono : monotone (@d P _) :=
λ A B h p hp q hAq, hp _ (h _ hAq)

def gc : galois_connection (@u P _) d :=
begin
  intros A B,
  dsimp [u, d],
  split,
  { intros h x hxA y hyB,
    apply h,
    assumption,
    assumption },
  { intros h x hxA y hyB,
    apply h,
    assumption,
    assumption }
end

lemma le_d_u (A : presheaf P) : A ≤ d (u A) := gc.le_u_l A
lemma u_d_le (A : copresheaf P) : u (d A) ≤ A := gc.l_u_le A

variable (P)

structure completion : Type :=
( to_presheaf : presheaf P )
( to_copresheaf : copresheaf P )
( d_to_copresheaf : d to_copresheaf = to_presheaf )
( u_to_presheaf : u to_presheaf = to_copresheaf )

attribute [simp] completion.d_to_copresheaf completion.u_to_presheaf

variable {P}

instance : partial_order (completion P) :=
partial_order.lift completion.to_copresheaf 
  begin
    rintros ⟨_, _, h₁, _⟩ ⟨_, _, h₂, _⟩,
    simp [← h₁, ← h₂] {contextual := tt}
  end

@[simp] lemma u_d_u (A : presheaf P) : (u (d (u A))) = (u A) :=
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

@[simp] lemma d_u_d (A : copresheaf P) : d (u (d A)) = d A :=
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

@[simp] lemma u_yoneda (p : P) : u (yoneda p) = coyoneda p :=
begin
  rw [u],
  conv_lhs {dsimp [coyoneda]},
  simp only [yoneda_le_iff],
  refl
end

@[simp] lemma d_coyoneda (p : P) : d (coyoneda p) = yoneda p :=
begin
  rw [d],
  conv_lhs {dsimp only [yoneda]},
  simp only [le_coyoneda_iff],
  refl
end

lemma le_iff_to_copresheaf {A B : completion P} : 
  (A ≤ B) ↔ (A.to_copresheaf ≤ B.to_copresheaf) := iff.rfl

lemma le_iff_to_presheaf {A B : completion P} : 
  (A ≤ B) ↔ (A.to_presheaf ≤ B.to_presheaf) := 
begin
  rw [le_iff_to_copresheaf],
  split,
  { intro h,
    rw [← completion.d_to_copresheaf, ← completion.d_to_copresheaf],
    exact d_mono h },
  { intro h,
    rw [← completion.u_to_presheaf, ← completion.u_to_presheaf],
    exact u_mono h }
end

def presheaf.to_completion (A : presheaf P) : completion P :=
⟨d (u A), u A, by simp, by simp⟩

def copresheaf.to_completion (A : copresheaf P) : completion P :=
⟨d A, u (d A), by simp, by simp⟩

def to_completion (p : P) : completion P :=
⟨yoneda p, coyoneda p, by simp, by simp⟩

@[simp] lemma presheaf.to_completion_to_presheaf (p : completion P) : p.to_presheaf.to_completion = p :=
begin
  cases p,
  simp [completion.to_presheaf, presheaf.to_completion, *],
end

@[simp] lemma copresheaf.to_completion_to_copresheaf (p : completion P) : p.to_copresheaf.to_completion = p :=
begin
  cases p,
  simp [completion.to_copresheaf, copresheaf.to_completion, *],
end

@[simp] lemma to_completion_to_presheaf (p : P) : (to_completion p).to_presheaf = yoneda p := rfl

@[simp] lemma to_completion_to_copresheaf (p : P) : (to_completion p).to_copresheaf = coyoneda p := rfl

variables {P}

def gi : galois_insertion (@presheaf.to_completion P _) (completion.to_presheaf) :=
galois_connection.to_galois_insertion 
  (λ A B, begin
    split,
    { simp [presheaf.to_completion, le_iff_to_presheaf, d, u, coyoneda, presheaf.le_def, yoneda],
      intros h p hAp,
      apply h,
      intros q hq,
      apply hq,
      exact hAp },
    { intro h,
      simp [presheaf.to_completion, le_iff_to_presheaf],
      rw [← B.d_to_copresheaf, ← B.u_to_presheaf],
      refine d_mono (u_mono h) }
  end)
  (by simp [presheaf.to_completion, le_iff_to_presheaf])

def gci : galois_coinsertion (completion.to_copresheaf) (@copresheaf.to_completion P _) :=
galois_connection.to_galois_coinsertion 
  (λ A B, begin
    split,
    { intro h,
      simp [copresheaf.to_completion, le_iff_to_copresheaf],
      rw [← A.u_to_presheaf, ← A.d_to_copresheaf],
      exact u_mono (d_mono h) },
    { simp [copresheaf.to_completion, le_iff_to_copresheaf, d, u, coyoneda, copresheaf.le_def, yoneda],
      intros h p hAp,
      apply h,
      intros q hq,
      apply hq,
      exact hAp },
  end)
  (by simp [copresheaf.to_completion, le_iff_to_copresheaf])

instance : complete_lattice (completion P) :=
galois_insertion.lift_complete_lattice gi

lemma completion.supr_def {ι : Sort*} (a : ι → completion P) : (⨆ i : ι, a i).to_copresheaf = 
  (⨆ i, (a i).to_copresheaf) :=
(@gci P _).gc.l_supr

lemma completion.infi_def {ι : Sort*} (a : ι → completion P) : (⨅ i : ι, a i).to_presheaf = 
  (⨅ i, (a i).to_presheaf) :=
(@gi P _).gc.u_infi

variables {Q : Type} [complete_lattice Q] (f : P → Q) (hf : monotone f)

include hf

def ump : completion P → Q :=
λ A, ⨆ (p : P) (h : A.to_presheaf p), f p

lemma ump_monotone : monotone (ump f hf) :=
begin
  intros A B hAB,
  dsimp [ump],
  simp only [supr_le_iff, le_supr_iff],
  intros x h p hp,
  apply h,
  apply hAB,
  apply hp
end

lemma ump_le (a : completion P) (x : P) : f x ≤ ump f hf a ↔ a.1 x :=
begin
  simp [ump, supr_le_iff, le_supr_iff, infi_le_iff],
  split,
  { intros h,
    
     },
  { intros ha p hap,
    apply hap,
    exact ha }
end

lemma ump_infi {ι : Sort*} (a : ι → completion P) : ump₁ f hf (infi a) = ⨅ i, ump₁ f hf (a i) :=
begin
  apply le_antisymm,
  { admit },
  { simp only [ump₁, umpp, le_supr_iff, supr_le_iff, infi_le_iff, le_infi_iff,
      to_completion, le_def, yoneda, presheaf.le_def],
    intros p h B h₂,
    apply h,
    intros i hi,
    apply h₂,

    apply h₂,  }
end

lemma ump_supr {ι : Sort*} (a : ι → completion P) : ump f hf (supr a) = ⨆ i, ump f hf (a i) :=
begin
  apply le_antisymm,
  { simp only [ump, umpp, le_supr_iff, supr_le_iff, infi_le_iff, le_infi_iff],
    intros x h₁ y h₂,
    apply h₂,
    intros z hz,
    apply h₁,
    intro i,
    apply hz, },
  { simp only [ump, umpp, le_supr_iff, supr_le_iff, infi_le_iff, le_infi_iff],
    intros i p h x hx,
    apply hx,
    apply p}
end