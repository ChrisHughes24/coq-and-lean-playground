import order.galois_connection
import data.set_like.basic

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

@[simp] lemma presheaf.le_def {A B : presheaf P} : A ≤ B = ∀ x, A x → B x := rfl

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

def copresheaf : Type := 
{ s : set P // ∀ a b, a ≤ b → s a → s b }

instance : has_coe_to_fun (copresheaf P) (λ _, P → Prop) :=
⟨subtype.val⟩

@[simp] lemma copresheaf.coe_mk (s : P → Prop) (hs : ∀ a b, a ≤ b → s a → s b) :
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

@[simp] lemma copresheaf.le_def {A B : copresheaf P} : A ≤ B = ∀ x, B x → A x := rfl

variable {P}

def u (A : presheaf P) : copresheaf P :=
⟨λ p, ∀ x, A x → x ≤ p, λ a b hab h x hxA, le_trans (h _ hxA) hab⟩

def d (B : copresheaf P) : presheaf P :=
⟨λ q, ∀ y, B y → q ≤ y, λ a b hab h x hxA, le_trans hab (h _ hxA)⟩

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

variable (P)

def completion : Type :=
{ A : presheaf P // A = d (u A) }

lemma d_u_sup {ι : Sort*} (A : ι → completion P) : d (u (⨆ i, (A i).1)) = ⨆ i, (A i).1 :=
begin
  refine le_antisymm _ _,
  { dsimp [d, u],
    intros x h,
    

   },
  { rw [← gc.le_iff_le],
    refine gc.monotone_l _,
    exact le_refl _ }
end

instance : partial_order (completion P) :=
partial_order.lift subtype.val subtype.val_injective

def Sup (s : set (completion P)) : completion P :=
⟨⨆ (A : completion P) (hA : A ∈ s), A.1, begin
  ext,
  dsimp,
  
  
end⟩

