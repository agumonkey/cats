------------------------------------------------------------------------------
-- Abel: A brother of Cain                https://github.com/jpvillaisaza/abel
--
--
------------------------------------------------------------------------------

{-# OPTIONS --no-universe-polymorphism #-}
{-# OPTIONS --without-K                #-}

module Abel.Function.Category where

open import Abel.Category.Category using (Category; mkCategory)
open import Abel.Function using (_⇒_)

open import Data.Product using (_,_)

open import Function using (id; _∘_)

open import Relation.Binary.PropositionalEquality using (refl)

------------------------------------------------------------------------------
--

category : Category _⇒_
category = mkCategory id (λ g f → g ∘ f) (λ _ → refl) (refl , refl)
