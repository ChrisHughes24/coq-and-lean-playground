import tactic

variables (P : Type) [partial_order P]

def presheaf : Type :=
{ s : P → Prop // ∀ a b, a ≤ b → s b → s a }

instance : has_coe_to_fun (presheaf P) (λ _, P → Prop) :=
⟨subtype.val⟩

@[simp] lemma presheaf.coe_mk (s : P → Prop) (hs : ∀ a b, a ≤ b → s b → s a) :
  @coe_fn (presheaf P) _ _ (⟨s, hs⟩ : presheaf P) = s := rfl

instance : partial_order (presheaf P) :=
{ le := λ A B, ∀ x, A x → B x,
  le_trans := λ A B C hAB hBC x hAx, hBC _ (hAB _ hAx),
  le_refl := λ A x, id,
  le_antisymm := λ A B hAB hBA, subtype.val_injective (funext $ λ x, propext ⟨hAB _, hBA _⟩) }

lemma presheaf.le_def {A B : presheaf P} : A ≤ B = ∀ x, A x → B x := rfl

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

variable {P}

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

@[simp] lemma yoneda_mono {a b : P} : yoneda a ≤ yoneda b ↔ a ≤ b :=
begin
  rw yoneda_le_iff, refl,
end

lemma eq_supr (A : presheaf P) : A = ⨆ (p : P) (h : A p), yoneda p :=
begin
  apply le_antisymm; simp only [le_supr_iff, supr_le_iff, yoneda_le_iff],
  { intros B hB p,
    exact hB p },
  { exact λ _, id }
end

lemma supr_eq_supr {ι : Sort*} (a : ι → presheaf P) : supr a = ⨆ (p : P) (i : ι) (h : a i p), yoneda p :=
begin
  rw [eq_supr (supr a)],
  apply le_antisymm,
  { simp only [le_supr_iff, supr_le_iff, yoneda_le_iff],
    intros p h,
    simp only [supr_def, yoneda_le_iff],
    simp only [supr_def] at *,
    cases i
    dsimp [yoneda], }


end  

variables {A : Type*} [complete_lattice A] (f : P → A) (hf : monotone f)

include hf

def ump : presheaf P → A :=
λ A, ⨆ (p : P) (h : A p), f p

lemma ump_supr {ι : Sort*} (a : ι → presheaf P) : ump f hf (supr a) = ⨆ i, ump f hf (a i) :=
begin
  apply le_antisymm,
  { simp only [ump, le_supr_iff, supr_le_iff],
    intros x hx y hy,
    simp only [supr_def] at *,
    dsimp at *,
    rcases hx with ⟨i, hi⟩,
    apply hy,
    apply hi },
  { simp only [ump, le_supr_iff, supr_le_iff],
    intros i p hap x h,
    apply h,
    rw [supr_def],
    dsimp,
    use i,
    use hap }
end