module Homomorphism

import Syntax.PreorderReasoning

--Thanks to David Christiansen from the Idris mailing list for fixing this.

data Hom : (a, b : Type) -> Semigroup a -> Semigroup b -> Type where
  MkHom : (actxt : Semigroup a, bctxt : Semigroup b) => (h : a -> b) -> 
          (preservesGroup : (a1 : a) -> (a2 : a) -> h ((<+>) @{actxt} a1 a2) = (<+>) @{bctxt} (h a1) (h a2)) -> Hom a b actxt bctxt


homRefl : (as : Semigroup a) => Hom a a as as
homRefl = MkHom id (\x,y => Refl) 

homTrans : (adict : Semigroup a, bdict : Semigroup b, cdict : Semigroup c) =>
           Hom a b adict bdict -> Hom b c bdict cdict -> Hom a c adict cdict
homTrans @{adict} @{bdict} @{cdict} (MkHom h preservesGroup) (MkHom h' preservesGroup') =
  MkHom @{adict} @{cdict} (\x => h' (h x)) 
                          (\something, another =>
                            (h' (h (something <+> another))) ={ ?prf1 }=
                            (h' (h something <+> h another)) ={ ?prf2 }=
                            (h' (h something) <+> h' (h another)) QED)

---------- Proofs ----------

Homomorphism.prf2 = proof
  intros
  rewrite preservesGroup' (h something) (h another)
  trivial


Homomorphism.prf1 = proof
  intros
  rewrite preservesGroup something another 
  trivial


