import order.complete_lattice
import set_theory.ordinal
import data.nat.prime

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

def extend {B : Type*} [complete_lattice B] (f : A → B) : presheaf A → B :=
λ a, ⨆ (p : A) (h : a p), f p

lemma extend_yoneda {B : Type*} [complete_lattice B] (f : A → B) (a : A)
  (hf : monotone f) : extend f (yoneda a) = f a :=
begin
  dsimp [extend, yoneda],
  apply le_antisymm,
  { refine supr_le (λ b, supr_le (λ h, hf h)) },
  { refine le_supr_iff.2 (λ b hb, _),
    refine le_trans _ (hb a),
    refine le_supr_iff.2 (λ b hb, hb le_rfl) }
end

lemma extend_supr {B : Type*} {ι : Sort*} [complete_lattice B] (f : A → B) (a : ι → presheaf A) :
  extend f (supr a) = ⨆ i, extend f (a i) :=
begin
  dsimp [extend],
  apply le_antisymm; 
  simp only [le_supr_iff, supr_le_iff, presheaf.supr_def]; 
  dsimp;
  simp only [exists_imp_distrib],
  { intros b i hbi c h,
    exact h _ _ hbi },
  { intros i b hbi c h,
    exact h _ _ hbi }
end

def total : presheaf (presheaf A) →o presheaf A :=
{ to_fun := λ F, ⟨λ X, F (yoneda X), begin
    intros B C hBC x,
    exact F.2 _ _ (yoneda_mono.2 hBC) x
  end⟩,
  monotone' := λ F G hFG a hF, hFG _ hF }

def map (f : A → B) : presheaf A → presheaf B :=
extend (λ a, yoneda (f a))

def map_total (f : A → B) (F : presheaf (presheaf A)) : map f (total F) = total (map (map f) F) :=
begin
  dsimp [map, extend, total],
  apply le_antisymm,
  { simp only [supr_le_iff, presheaf.supr_def, presheaf.le_def],
    simp,
    intros b a ha hb,
    use yoneda a,
    use ha,
    dsimp [yoneda, presheaf.le_def] at *,
    intros x hxb,
    use a,
    use le_rfl,
    use le_trans hxb hb },
  { simp only [le_supr_iff, presheaf.supr_def, presheaf.le_def],
    simp [yoneda],
    intros a b ha h,
    cases h le_rfl with x hx,
    use x,split,
    refine F.2 _ _ _ ha,
    simp [presheaf.le_def],
    intros y hy,
    exact b.2 _ _ hy hx.1,
    exact hx.2
     }

end 

def comp (f : A →o B) : presheaf B → presheaf A :=
λ b, ⟨λ a, b (f a), λ x y hxy, b.2 _ _ $ f.monotone hxy⟩

example (f : A →o B) : galois_connection (map f) (comp f):=
begin
  intros x y,
  simp [map, comp, extend, supr_le_iff, presheaf.le_def, presheaf.supr_def, yoneda],
  split,
  { intros h a hxa, exact h _ _ hxa le_rfl },
  { intros h b a hxa hba,
    exact y.2 _ _ hba (h _ hxa) }
end

variables {A' : Type*} [complete_lattice A'] [B' : Type*] [complete_lattice B']
  (i : A → A') (j : B → B') (hi : monotone i) (hj : monotone j)
include hi hj

example (f : A → B) (hf : monotone f) (g : presheaf B → presheaf A)
  (h : galois_connection (map f) g)
  (f' : A' → B') (g' : B' → A') (gc : galois_connection f' g')
  (hfij : ∀ x, f' (i x) = j (f x)) :
  g' ∘ extend j = extend i ∘ g :=
-- have hg : g = (λ b, ⨆ (c : presheaf A) (h : map f c ≤ b), c), 
--   begin
--     funext b,
--     apply le_antisymm,
--     { simp only [le_supr_iff, supr_le_iff],
--       intros c hc,
--       refine hc _ _,
--       exact h.l_u_le _ },
--     { refine supr_le (λ c, supr_le (λ hc, h.le_iff_le.1 hc)) },
--   end,
have hg : g = comp ⟨f, hf⟩ := 
  begin
    apply le_antisymm,
    intro x,
    swap,
    intro x,
    rw [← h.le_iff_le],
    simp [comp, map],
    intro a,
    simp [extend, yoneda, presheaf.supr_def],
    intros,
    apply x.2 _ (f x_1),
    assumption, assumption,
    simp [comp],
    intro a,
    intro h1,
    rw [← yoneda_le_iff, ← h.le_iff_le] at h1,
    simp [yoneda, map, extend] at *,
    apply h1,
    apply le_rfl,
    simp,
    
  end,
have hg' : g' = (λ b, ⨆ (c : A') (h : f' c ≤ b), c), 
  begin
    funext b,
    apply le_antisymm,
    { simp only [le_supr_iff, supr_le_iff],
      intros c hc,
      refine hc _ _,
      exact gc.l_u_le _ },
    { refine supr_le (λ c, supr_le (λ hc, gc.le_iff_le.1 hc)) },
  end,
begin
  funext a,
  dsimp,
  substs g g',
  rw [eq_supr a],
  simp only [extend_supr, extend_yoneda _ _ hj],
  simp [extend, comp, presheaf.supr_def, yoneda],
  apply le_antisymm,
  { simp only [le_supr_iff, supr_le_iff],
    intros x hx y hy,
    refine le_trans (gc.le_iff_le.1 (hx ⊤ _)) _,
    { intros b hai,
      exact le_top,
       },
    simp only [supr_le_iff], admit,
     },
  { simp only [le_supr_iff, supr_le_iff],
    intros b c hbc x hx,
    apply hx,
    intros d hd,
    rw [hfij],
    apply hd,
    refine a.2 _ _ hbc.2 hbc.1 }
end


example (f : A → B) (hf : monotone f) (g : presheaf B → presheaf A)
  (h : galois_connection (map f) g)
  (f' : A' → B') (g' : B' → A') (gc : galois_connection f' g')
  (hfij : ∀ x, f' (i x) ≤ j (f x)) :
  extend i ∘ g ≤ g' ∘ extend j :=
have hg : g = comp ⟨f, hf⟩ := sorry,
have hg' : g' = (λ b, ⨆ (c : A') (h : f' c ≤ b), c), 
  begin
    funext b,
    apply le_antisymm,
    { simp only [le_supr_iff, supr_le_iff],
      intros c hc,
      refine hc _ _,
      exact gc.l_u_le _ },
    { refine supr_le (λ c, supr_le (λ hc, gc.le_iff_le.1 hc)) },
  end,
begin
  intros a,
  dsimp,
  substs g g',
  simp only [extend_supr, extend_yoneda _ _ hj],
  simp [extend, comp, presheaf.supr_def, yoneda],
  { simp only [le_supr_iff, supr_le_iff],
    intros b hb x hx,
    apply hx,
    intros d hd,
    refine le_trans (hfij _) _,
    apply hd,
    exact hb }
end

example : false :=
begin
  have := @thing ℕ ℕ _ _,

end

example (f : A → B) (hf : monotone f) (g : presheaf B → presheaf A) 
  (h : galois_connection g (map f))
  (f' : A' → B') (g' : B' → A') (gc : galois_connection g' f') 
  (hfij : f' ∘ i = j ∘ f) : 
  g' ∘ extend j = extend i ∘ g :=
-- have hg : g = (λ b, ⨆ (c : presheaf A) (h : map f c ≤ b), c), 
--   begin
--     funext b,
--     apply le_antisymm,
--     { simp only [le_supr_iff, supr_le_iff],
--       intros c hc,
--       refine hc _ _,
--       exact h.l_u_le _ },
--     { refine supr_le (λ c, supr_le (λ hc, h.le_iff_le.1 hc)) },
--   end,
have hfij' : f' ∘ extend i = extend j ∘ map f :=
begin
  funext x,
  dsimp [extend, gc.l_supr],
end,
have hg : g = comp ⟨f, hf⟩ := sorry,
have hg' : g' = (λ b, ⨆ (c : A') (h : f' c ≤ b), c), 
  begin
    funext b,
    apply le_antisymm,
    { simp only [le_supr_iff, supr_le_iff],
      intros c hc,
      refine hc _ _,
      exact gc'.l_u_le _ },
    { refine supr_le (λ c, supr_le (λ hc, gc.le_iff_le.1 hc)) },
  end,
begin
  funext a,
  dsimp,
  substs g g',
  rw [eq_supr a],
  simp only [extend_supr, extend_yoneda _ _ hj],
  simp [extend, comp, presheaf.supr_def, yoneda],
  apply le_antisymm,
  { simp only [le_supr_iff, supr_le_iff],
    intros x hx y hy, }
  
 

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
    exact hB p }
end

def extend {B : Type*} [complete_lattice B] (f : A → B) : copresheaf A → B :=
λ a, ⨅ (p : A) (h : a p), f p

def blah1 (M : copresheaf (A × order_dual B)) : A →o presheaf B :=
{ to_fun := λ a, ⟨λ b, M (a, order_dual.to_dual b), 
    λ x y hxy hM, M.2 (a, order_dual.to_dual y) _ ⟨le_rfl, hxy⟩ hM⟩,
  monotone' := λ x y hxy a ha, begin
    dsimp at *,
    refine M.2 (x, order_dual.to_dual a) _ _ _,
    split, exact hxy, refl, assumption 
  end, }

def blah2 (M : copresheaf (A × order_dual B)) : B →o copresheaf A :=
{ to_fun := λ b, ⟨λ a, M (a, order_dual.to_dual b), 
    λ x y hxy hM, M.2 (x, order_dual.to_dual b) _ ⟨hxy, le_rfl⟩ hM⟩,
  monotone' := λ x y hxy a ha, begin
    dsimp at *,
    refine M.2 (a, order_dual.to_dual y) _ _ _,
    split, refl, assumption, assumption
  end, }

example  
  {A' B' : Type} [complete_lattice A'] [complete_lattice B'] 
  (M : copresheaf (A × order_dual B))
  (f : A' → B') (g : B' → A') 
  (gc : galois_connection g f)
  (i : A → A') (j : B → B') (hi : monotone i) (hj : monotone j)
  (hf : ∀ x, f (i x) = presheaf.extend j (blah1 M x)) : 
  ∀ x, g (j x) = copresheaf.extend i (blah2 M x) :=
begin
  intros x,
  dsimp [presheaf.extend, copresheaf.extend, blah1, blah2] at *,
  apply le_antisymm,
  { simp only [le_infi_iff],
    intros a ha,
    rw [gc.le_iff_le],
    rw hf,
    simp only [le_supr_iff, supr_le_iff],
    intros b hb,
    apply hb,
    exact ha },
  { simp only [infi_le_iff, le_infi_iff],
    intros a ha,
     }

end

example  
  {A' B' : Type} [complete_lattice A'] [complete_lattice B'] 
  (M : copresheaf (A × order_dual B))
  (f : A' → B') (g : B' → A') 
  (gc : galois_connection f g)
  (i : A → A') (j : B → B') (hi : monotone i) (hj : monotone j)
  (hf : ∀ x, f (i x) = presheaf.extend j (blah1 M x)) : 
  ∀ x, g (j x) = copresheaf.extend i (blah2 M x) :=
begin
  intros x,
  dsimp [presheaf.extend, copresheaf.extend, blah1, blah2] at *,
  apply le_antisymm,
  { admit },
  { simp only [infi_le_iff, le_infi_iff],
    intros a ha,
    rw [← gc.le_iff_le],
     }

end
  

example {A' B' : Type} [complete_lattice A'] [complete_lattice B'] 
  (f : A → B) (hf : monotone f) 
  (f' : A' → B') (g' : B' → A') (gc : galois_connection f' g') 
  (h1 : ) :

end copresheaf

open presheaf copresheaf

variables (f : A ↪o B) (hf : ∀ b, { s : set A // is_glb (f '' s) b})

namespace presheaf

def u (a : presheaf B) : copresheaf B :=
⟨λ p, coyoneda a (yoneda p), λ a b hab h x hxA, le_trans (h _ hxA) hab⟩

lemma u_mono : monotone (@u B _):=
λ A B h p hp q hAq, hp _ (h _ hAq)

include hf

def d (a : copresheaf B) : presheaf B :=
⟨λ q, ∀ (x : A), a (f x) → q ≤ f x, λ a b hab h x hxA, le_trans hab (h _ hxA)⟩

lemma d_mono : monotone (d f hf) :=
λ A B h p hp q hAq, hp _ (h _ hAq)

def gc : galois_connection u (d f hf) :=
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

omit hf

open copresheaf

@[simp] lemma le_d_u (a : presheaf B) : a ≤ d f hf (u a) := (gc f hf).le_u_l a

@[simp] lemma u_d_u (a : presheaf B) : u (d f hf (u a)) = u a :=
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

lemma u_d_le (a : copresheaf B) : u (d f hf a) ≤ a := (gc f hf).l_u_le a

@[simp] lemma d_u_d (a : copresheaf B) : d f hf (u (d f hf a)) = d f hf a :=
(gc f hf).u_l_u_eq_u _

include hf

@[simp] lemma d_coyoneda (p : B) : d f hf (coyoneda p) = yoneda p :=
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

/- Aiming to construct a pscompletion of `B` that preserves all sups in `A`.
  So if we have a partial order `C` a monotone function `B -> C` and a `sup_hom`
  from `A -> C` that commute with `f` there is a unique cocontinuous map from
  the pscompletion to `C` such that everything commutes. -/

structure pscompletion : Type v :=
( to_presheaf : presheaf B )
( fixed : d f hf (u to_presheaf) = to_presheaf )

namespace pscompletion

variables {B}

def _root_.presheaf.to_pscompletion (a : presheaf B) : pscompletion f hf :=
⟨d f hf (u a), by simp *⟩

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

lemma supr_to_presheaf {ι : Sort*} (a : ι → pscompletion f hf) : 
  (supr a).to_presheaf = d f hf (⨆ i, (a i).to_presheaf).u :=
begin 
  rw ← (gi f hf).l_supr_u, refl,
end

@[simps] def of_partial_order (a : B) : pscompletion f hf :=
⟨yoneda a, by rw [u_yoneda, d_coyoneda f hf]⟩

@[simp] lemma of_partial_order_mono {a b : B} : of_partial_order f hf a ≤ of_partial_order f hf b ↔ a ≤ b :=
yoneda_mono

lemma of_partial_order_le_iff (a : B) (x : pscompletion f hf) : 
  of_partial_order f hf a ≤ x ↔ x.to_presheaf a :=
by simp only [of_partial_order, le_def, yoneda_le_iff]

lemma of_partial_order_lub (s : set A) (a : A) (h : is_lub s a) : 
  is_lub (of_partial_order f hf '' (f '' s)) (of_partial_order f hf (f a)) :=
begin
  split,
  { simp only [upper_bounds, set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, set.mem_set_of_eq,
      of_partial_order_mono],
    intros b hbs,
    exact f.monotone (h.1 hbs) },
  { simp only [upper_bounds, lower_bounds, set.mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      set.mem_set_of_eq],
    intros x hx,
    cases x with x x_fixed,
    refine (yoneda_le_iff _ _).2 _,
    dsimp,
    simp only [le_def, of_partial_order_to_presheaf, yoneda_le_iff] at hx,
    rw [← x_fixed],
    dsimp [d, u],
    intros b hb,
    simp [coyoneda, presheaf.le_def, yoneda] at hb,
    refine f.monotone _,
    apply h.2,
    intros c hc,
    apply f.le_iff_le.1,
    apply hb,
    apply hx,
    exact hc }
end

variables {C : Type*} [complete_lattice C] (i : B →o C)

def ump : pscompletion f hf → C :=
λ x, ⨆ (b : B) (h : x.to_presheaf b), i b

lemma ump_supr {ι : Sort*} (a : ι → pscompletion f hf) : ump f hf i (supr a) = ⨆ j, ump f hf i (a j) :=
begin
  dsimp [ump],
  simp only [supr_to_presheaf],
  simp only [of_partial_order_le_iff, le_antisymm_iff, supr_le_iff, le_supr_iff],
  split,
  { intros c h₁ b h₂,
    simp [d, u, coyoneda, yoneda, le_def, presheaf.le_def, presheaf.supr_def] at h₂,
    apply h₁,
    apply h₂,
    intros i, admit,  admit},
  { intros c h₁ j b h₂,
    apply h₁,
    intros x h,
    refine h j _ _,
    exact h₂ }
end

end pscompletion