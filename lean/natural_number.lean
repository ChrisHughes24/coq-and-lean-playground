constant N : Type

constant zero : N

constant succ : N → N

universe u

@[elab_as_eliminator] 
constant parametric {motive : N → N → Sort u} 
  (h0 : motive zero zero) (h1 : Π n m, motive n m → motive (succ n) (succ m)) :
  Π (n m), motive n m

noncomputable theory

@[elab_as_eliminator]
def N.rec_on {motive : N → Sort u} (h0 : motive zero) 
  (h1 : Π (n : N), motive n → motive (succ n)) (n : N) : motive n :=
parametric h0 (λ _, h1) n n

lemma N.rec_on_zero {motive : N → Sort u} (h0 : motive zero) 
  (h1 : Π (n : N), motive n → motive (succ n)) : 
  @N.rec_on motive h0 h1 zero = h0 :=
begin


end