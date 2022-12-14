import tactic
import category_theory.functor
import data.W.basic
import category_theory.closed.types
import algebra.category.CommRing.basic
import algebra.category.Module.basic

universes w x u v 

open category_theory

variables (ð : Type u) [category.{v} ð]

@[protect_proj] structure struc : Type (max u v (w+1) (x+1)) :=
( F : ð â Type w )
( F_iso : Î  {A B : ð}, (A â B) â F A â F B )
( F_iso_refl : Î  {A : ð}, F_iso (iso.refl A) = equiv.refl (F A) )
( F_iso_trans : Î  {A B C : ð} (eâ : A â B) (eâ : B â C), 
    equiv.trans (F_iso eâ) (F_iso eâ) = F_iso (iso.trans eâ eâ) )
( hom : Î  {A B : ð} (f : A â¶ B) (a : F A) (b : F B), Type x )
( hom_iso : Î  {Aâ Aâ Bâ Bâ : ð} 
    (fâ : Aâ â¶ Bâ) (aâ : F Aâ) (bâ : F Bâ)
    (fâ : Aâ â¶ Bâ) (aâ : F Aâ) (bâ : F Bâ)
    (eA : Aâ â Aâ) (eB : Bâ â Bâ)
    (hf : fâ â« eB.hom = eA.hom â« fâ)
    (ha : aâ = F_iso eA aâ)
    (hb : bâ = F_iso eB bâ),
    hom fâ aâ bâ â hom fâ aâ bâ )
( hom_iso_refl : Î  {A B : ð} 
    (f : A â¶ B) (a : F A) (b : F B)
    (hf : f â« (iso.refl B).hom = (iso.refl A).hom â« f)
    (ha : a = F_iso (iso.refl A) a)
    (hb : b = F_iso (iso.refl B) b),
    hom_iso f a b f a b (iso.refl A) (iso.refl B) hf ha hb = equiv.refl (hom f a b) )
( hom_iso_trans : Î  {Aâ Aâ Aâ Bâ Bâ Bâ : ð}
    (fâ : Aâ â¶ Bâ) (aâ : F Aâ) (bâ : F Bâ)
    (fâ : Aâ â¶ Bâ) (aâ : F Aâ) (bâ : F Bâ)
    (fâ : Aâ â¶ Bâ) (aâ : F Aâ) (bâ : F Bâ) 
    (eAââ : Aâ â Aâ) (eBââ : Bâ â Bâ)
    (eAââ : Aâ â Aâ) (eBââ : Bâ â Bâ)
    (hfââ : fâ â« eBââ.hom = eAââ.hom â« fâ)
    (hfââ : fâ â« eBââ.hom = eAââ.hom â« fâ)
    (haââ : aâ = F_iso eAââ aâ)
    (haââ : aâ = F_iso eAââ aâ)
    (hbââ : bâ = F_iso eBââ bâ)
    (hbââ : bâ = F_iso eBââ bâ),
    (hom_iso fâ aâ bâ fâ aâ bâ eAââ eBââ hfââ haââ hbââ).trans
    (hom_iso fâ aâ bâ fâ aâ bâ eAââ eBââ hfââ haââ hbââ) =
    hom_iso fâ aâ bâ fâ aâ bâ (eAââ.trans eAââ) (eBââ.trans eBââ) 
      (by simp [â hfââ, â hfââ, category.assoc]) 
      (by simp [haââ, haââ, â F_iso_trans]) 
      (by simp [hbââ, hbââ, â F_iso_trans]) )
( id : Î  {A : ð} (a : F A), hom (ð A) a a )
( hom_iso_id : Î  {Aâ Aâ : ð}
    (aâ : F Aâ) (aâ : F Aâ)
    (eA : Aâ â Aâ)
    (hf : ð Aâ â« eA.hom = eA.hom â« ð Aâ)
    (ha : aâ = F_iso eA aâ),
    hom_iso (ð Aâ) aâ aâ (ð Aâ) aâ aâ eA eA hf ha ha (id aâ) = id aâ )
( comp : Î  {A B C : ð} {a : F A} {b : F B} {c : F C}
    {f : A â¶ B} {g : B â¶ C} (f' : hom f a b) (g' : hom g b c), 
    hom (f â« g) a c )
( hom_iso_comp : Î  {Aâ Aâ Bâ Bâ Câ Câ}
    (fâ : Aâ â¶ Bâ) (gâ : Bâ â¶ Câ) (aâ : F Aâ) (bâ : F Bâ) (câ : F Câ)
    (fâ : Aâ â¶ Bâ) (gâ : Bâ â¶ Câ) (aâ : F Aâ) (bâ : F Bâ) (câ : F Câ)
    (eA : Aâ â Aâ) (eB : Bâ â Bâ) (eC : Câ â Câ)
    (hf : fâ â« eB.hom = eA.hom â« fâ)
    (hg : gâ â« eC.hom = eB.hom â« gâ)
    (hfg : (fâ â« gâ) â« eC.hom = eA.hom â« (fâ â« gâ))
    (ha : aâ = F_iso eA aâ)
    (hb : bâ = F_iso eB bâ)
    (hc : câ = F_iso eC câ)
    (fâ' : hom fâ aâ bâ)
    (gâ' : hom gâ bâ câ),
    hom_iso (fâ â« gâ) aâ câ (fâ â« gâ) aâ câ eA eC hfg
       ha hc (comp fâ' gâ') = 
      comp (hom_iso fâ aâ bâ fâ aâ bâ eA eB hf ha hb fâ') 
        (hom_iso gâ bâ câ gâ bâ câ eB eC  hg hb hc gâ') )
( id_comp : Î  {A B : ð} {f : A â¶ B} {a : F A} {b : F B}
    (f' : hom f a b), comp (id a) f' = hom_iso f a b (ð A â« f) a b (iso.refl A) (iso.refl B) 
      (by simp) (by rw F_iso_refl; refl) (by rw F_iso_refl; refl) f' )
( comp_id : Î  {A B : ð} {f : A â¶ B} {a : F A} {b : F B}
    (f' : hom f a b), comp f' (id b) = hom_iso f a b (f â« ð B) a b (iso.refl A) (iso.refl B) 
      (by simp) (by rw F_iso_refl; refl) (by rw F_iso_refl; refl) f' )
( assoc : Î  {A B C D : ð} {f : A â¶ B} {g : B â¶ C} {h : C â¶ D}
    {a : F A} {b : F B} {c : F C} {d : F D}
    (f' : hom f a b) (g' : hom g b c) (h' : hom h c d),
    comp (comp f' g') h' = hom_iso (f â« (g â« h)) a d ((f â« g) â« h) a d 
      (iso.refl A) (iso.refl D) (by simp) (by rw F_iso_refl; refl) (by rw F_iso_refl; refl)
      (comp f' (comp g' h')) )

namespace struc

instance : has_coe_to_fun (struc ð) (Î» _, ð â Type w) :=
{ coe := struc.F }

variables {ð}

-- @[protect_proj] class GS (F : ð â Type w) :=
-- ( hom : Î  {A B : ð} (f : A â¶ B) (a : F A) (b : F B), Type x )
-- ( id : Î  {A : ð} (a b : F A) (h : a = b) (f : A â¶ A) (hf : f = ð A), hom f a b )

attribute [simp] struc.id_comp struc.comp_id struc.hom_iso_refl struc.F_iso_refl struc.F_iso_trans
  struc.hom_iso_trans

variables (F : struc ð) 

-- lemma assoc_left {A B C D : ð} {f : A â¶ B} {g : B â¶ C} {h : C â¶ D}
--     {a : F A} {b : F B} {c : F C} {d : F D}
--     (f' : F.hom f a b) (g' : F.hom g b c) (h' : F.hom h c d)
--     (i : A â¶ C) (k : A â¶ D)
--     (hi : f â« g = i) (hk : i â« h = k) :
--     F.comp (F.comp f' g' hi) h' hk = F.comp f'
--       (F.comp g' h' rfl) (by rw [â hk, â hi, category.assoc]) :=
-- begin
--   substs i k,
--   rw struc.assoc,
-- end

-- lemma comp_eq_cast {A B C : ð} {f : A â¶ B} {g : B â¶ C} 
--   {a : F A} {b : F B} {c : F C} (f' : F.hom f a b) (g' : F.hom g b c)
--   (i : A â¶ C) (hi : f â« g = i)
--   (j : A â¶ C) (hj : f â« g = j) :
--   F.comp f' g' hi = cast (by substs i j) (F.comp f' g' hj) :=
-- begin
--   substs i j, refl
-- end

-- lemma assoc_left' {A B C D : ð} {f : A â¶ B} {g : B â¶ C} {h : C â¶ D}
--     {a : F A} {b : F B} {c : F C} {d : F D}
--     (f' : F.hom f a b) (g' : F.hom g b c) (h' : F.hom h c d)
--     (i : A â¶ C) (k : A â¶ D)
--     (hi : f â« g = i) (hk : i â« h = k) :
--     F.comp (F.comp f' g' hi) h' hk = cast (by rw [â hk, â hi, category.assoc]) 
--       (F.comp f' (F.comp g' h' rfl) rfl)  :=
-- begin
--   rw struc.assoc_left,
--   substs i k,
--   rw [comp_eq_cast]
-- end

-- lemma id_comp' {A B : ð} {f : A â¶ B} (g : A â¶ B) {a : F A} {b : F B}
--   (h : ð A â« f = g) (f' : F.hom f a b) : 
--   F.comp (F.id a) f' h = cast (by rw [â h, category.id_comp]) f' :=
-- begin
--   rw [category.id_comp] at h,
--   subst h,
--   simp
-- end

-- lemma comp_id' {A B : ð} {f : A â¶ B} (g : A â¶ B) {a : F A} {b : F B}
--   (h : f â« ð B = g) (f' : F.hom f a b) : 
--   F.comp f' (F.id b) h = cast (by rw [â h, category.comp_id]) f' :=
-- begin
--   rw [category.comp_id] at h,
--   subst h,
--   simp
-- end 

def sigmaâ (F : struc ð) : Type* := sigma F

instance : category_struct (sigmaâ F) :=
{ hom := Î» A B, Î£ (f : A.1 â¶ B.1), F.hom f A.2 B.2,
  id := Î» A, â¨ð A.1, F.id A.2â©,
  comp := Î» A B C f g, â¨f.1 â« g.1, F.comp f.2 g.2â© }

variable {F}

lemma sigmaâ.hom_ext {A B : sigmaâ F} {f g : A â¶ B} 
  (hâ : f.1 = g.1) (hâ : F.hom_iso f.1 A.2 B.2 g.1 A.2 B.2 
    (iso.refl A.1) (iso.refl B.1) (by simp *) (by simp *) (by simp *) f.2 = g.2) :
  f = g :=
begin
  cases A,
  cases B,
  cases f,
  cases g,
  dsimp at *,
  subst hâ,
  simp at hâ,
  subst hâ
end

def sigma_category : category_struct (sigma F) :=
{ hom := Î» A B, Î£ (f : A.1 â¶ B.1), F.hom f A.2 B.2,
  id := Î» A, â¨ð A.1, F.id A.2â©,
  comp := Î» A B C f g, â¨f.1 â« g.1, F.comp f.2 g.2â© }

@[simp] lemma comp_fst {A B C : sigmaâ F} (f : A â¶ B) (g : B â¶ C) :
  (f â« g).fst = f.1 â« g.1 := rfl

@[simp] lemma comp_snd {A B C : sigmaâ F} (f : A â¶ B) (g : B â¶ C) :
  (f â« g).snd = F.comp f.2 g.2 := rfl

@[simp] lemma id_fst {A : sigmaâ F} : sigma.fst (ð A) = ð A.1 := rfl

@[simp] lemma id_snd {A : sigmaâ F} : sigma.snd (ð A) = F.id A.2 := rfl

section

local attribute [instance] sigma_category

instance sigma.category : category (sigmaâ F) :=
{ id_comp' := Î» A B f, begin
      refine sigmaâ.hom_ext _ _,
      { simp },
      { simp,
        rw [â equiv.trans_apply], 
        erw F.hom_iso_trans,
        simp }
    end,
  comp_id' := Î» A B f, begin
      refine sigmaâ.hom_ext _ _,
      { simp },
      { simp,
        rw [â equiv.trans_apply], 
        erw F.hom_iso_trans,
        simp }
    end,
  assoc' := Î» A B C D f g h, begin
      refine sigmaâ.hom_ext _ _,
      { simp [category.assoc] },
      { simp [struc.assoc],
        rw â equiv.trans_apply,
        erw F.hom_iso_trans,
        simp,
        erw [F.hom_iso_refl], 
        refl }
    end, }

end

instance (X : ð) : category_struct (F X) :=
{ hom := Î» A B, F.hom (ð X) A B,
  id := Î» A, F.id A,
  comp := Î» A B C f g, F.hom_iso (ð X â« ð X) A C (ð X) A C (iso.refl X) (iso.refl X) 
    (by simp) (by simp) (by simp) (F.comp f g) }

lemma id_def {X : ð} (x : F X) : ð x = F.id x := rfl 

lemma comp_def (X : ð) (A B C : F X) (f : A â¶ B) (g : B â¶ C) :
  f â« g = F.hom_iso (ð X â« ð X) A C (ð X) A C (iso.refl X) (iso.refl X) 
    (by simp) (by simp) (by simp) (F.comp f g) := rfl

instance (X : ð) : category (F X) :=
{ id_comp' := Î» A B f, begin 
      simp [id_def, comp_def],
      rw [â equiv.trans_apply, F.hom_iso_trans],
      simp
    end,
  comp_id' := Î» A B f, begin 
      simp [id_def, comp_def],
      rw [â equiv.trans_apply, F.hom_iso_trans],
      simp
    end,
  assoc' := Î» A B C D f g h,
      begin
        simp only [comp_def, â F.hom_iso_comp],
        erw F.hom_iso_comp,
      end }

def forget : sigmaâ F â¥¤ ð :=
{ obj := sigma.fst,
  map := Î» _ _, sigma.fst }

def thing (X : ð) : F X â¥¤ sigmaâ F :=
{ obj := Î» A, â¨X, Aâ©,
  map := Î» A B f, â¨ð X, fâ©,
  map_id' := Î» A, rfl,
  map_comp' := Î» A B C f g, sigma.ext 
    (by simp) begin 
      simp only [comp_snd],
      rw [struc.comp_eq_cast F f g (ð X â« ð X) rfl (ð X)
        (category.comp_id _)],
      symmetry,
      rw [â cast_eq_iff_heq],
      simp, refl,
      simp,
    end }

open opposite

protected def op (F : struc ð) : struc ðáµáµ :=
{ F := Î» A, F.F (unop A),
  hom := Î» A B f a b, F.hom f.unop b a,
  id := Î» A a, F.id a,
  comp := Î» A B C a b c f g f' g' h hH, 
    F.comp g' f' (by simp [â hH]),
  id_comp := Î» A B f a b f', F.comp_id _,
  comp_id := Î» A B f a b f', F.id_comp _,
  assoc := Î» A B C D f g h a b c d f' g' h', 
    by rw F.assoc_left; refl }

def unop (F : struc ðáµáµ) : struc ð :=
{ F := Î» A, F.F (op A),
  hom := Î» A B f a b, F.hom f.op b a,
  id := Î» A a, F.id a,
  comp := Î» A B C a b c f g f' g' h hH, 
     F.comp g' f' (by simp [â hH]),
  id_comp := Î» A B f a b f', F.comp_id _,
  comp_id := Î» A B f a b f', F.id_comp _,
  assoc := Î» A B C D f g h a b c d f' g' h', 
    by rw F.assoc_left; refl }

def of_functor (F : ð â¥¤ Type w) : struc ð :=
{ F := F.obj,
  hom := Î» A B f a b, plift (F.map f a = b),
  id := Î» A a, â¨by simpâ©,
  comp := Î» A B C a b c f g hâ hâ _ h, â¨by simp [â h, F.map_comp, hâ.down, hâ.down]â©,
  assoc := Î» _ _ _ _ _ _ _ _ _ _ _ hâ hâ hâ, 
    begin simp [hâ.down, hâ.down, hâ.down] end,
  id_comp := Î» _ _ _ _ _ h, 
    begin simp [h.down] end,
  comp_id := Î» _ _ _ _ _ h, 
    begin simp [h.down] end }

def Moduleâ : struc Ring :=
{ F := Î» R, Module R,
  hom := Î» R S f Mâ Mâ, Mâ âââ[f] Mâ,
  id := Î» R M, linear_map.id,
  comp := Î» R S T Mâ Mâ Mâ f g f' g' _ h, 
    @linear_map.comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ â¨hâ© g' f',
  id_comp := Î» R S f Mâ Mâ f', begin
      cases f', cases f, refl
    end,
  comp_id := Î» R S f Mâ Mâ f', begin
      cases f', cases f, refl,
    end,
  assoc := Î» R S T U f g h Mâ Mâ Mâ Mâ f' g' h', 
    begin
      cases f, cases g, cases h, cases f', cases g', cases h',
      refl
    end }

def pi.struc (F : ð â¥¤ Type) (G : struc (sigmaâ (of_functor F))) : struc ð :=
{ F := Î» X, Î  a : F.obj X, G.F â¨X, aâ©,
  hom := Î» X Y f x y, Î  (a : F.obj X), 
    @struc.hom _ _ G â¨X, aâ© â¨Y, F.map f aâ© â¨f, â¨rflâ©â© (x a) (y (F.map f a)),
  id := Î» X x a, by convert (G.id (x a)); simp,
  comp := Î» X Y Z x y z f g f' g' h H a, 
    by convert struc.comp G (f' a) (g' (F.map f a)) rfl; subst H; simp,
  id_comp := Î» X a, begin
    intros,
    ext,
    simp,
    
  end }

-- Maybe think about W.

end struc