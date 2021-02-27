{-# OPTIONS --cubical #-}
module SK where
open import Level renaming (suc to 𝓁-suc)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe.Properties
open import Cubical.Foundations.Structure
open import Cubical.HITs.SetQuotients 
open import Cubical.HITs.SetQuotients.Base
open import Cubical.HITs.SetQuotients.Properties
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (elim to ⊥-elim)

private
  variable
    𝓁 : Level
    A : Set 𝓁

data SK : Set where
  S : SK
  K : SK
  _⋅_ : SK → SK → SK

infixl 7 _⋅_

data _↝β_ : SK → SK → Set where
  βK : ∀ {x y} → (K ⋅ x) ⋅ y ↝β x
  βS : ∀ {f g x} → ((S ⋅ f) ⋅ g) ⋅ x ↝β f ⋅ x ⋅ (g ⋅ x)
  βˡ : ∀ {x x′ y} → x ↝β x′ → x ⋅ y ↝β x′ ⋅ y
  βʳ : ∀ {x y y′} → y ↝β y′ → x ⋅ y ↝β x ⋅ y′

infixl 6 _↝β_

SKβ : Type₀
SKβ = SK / _↝β_

module _ where
  private
    variable
      R : A → A → Type 𝓁
  recQ : {B : Type 𝓁}
        (Bset : isSet B)
        (f : A → B)
        (feq : (a b : A) (r : R a b) → f a ≡ f b)
      → A / R → B
  recQ Bset f feq [ a ] = f a
  recQ Bset f feq (eq/ a b r i) = feq a b r i
  recQ Bset f feq (squash/ x y p q i j) = Bset (g x) (g y) (cong g p) (cong g q) i j
    where
    g = recQ Bset f feq

  rec2 : {B : Type 𝓁} (Bset : isSet B)
       (f : A → A → B) (feql : (a b c : A) (r : R a b) → f a c ≡ f b c)
                       (feqr : (a b c : A) (r : R b c) → f a b ≡ f a c)
    → A / R → A / R → B
  rec2 Bset f feql feqr = recQ (isSetΠ (λ _ → Bset))
                            (λ a → recQ Bset (f a) (feqr a))
                            (λ a b r → funExt (elimProp (λ _ → Bset _ _)
                                              (λ c → feql a b c r)))
SKβ-isSet : isSet SKβ
SKβ-isSet = squash/

_⊙_ : SKβ → SKβ → SKβ
_⊙_ = rec2 SKβ-isSet (λ x x₁ → [ x ⋅ x₁ ]) 
  (λ a b c a↝b → eq/ (a ⋅ c) (b ⋅ c) (βˡ a↝b)) 
  (λ a b c b↝c → eq/ (a ⋅ b) (a ⋅ c) (βʳ b↝c))

infixl 7 _⊙_

[S] : SKβ 
[S] = [ S ]

[K] : SKβ
[K] = [ K ]

SKK-identˡ : ∀ {x} → [S] ⊙ [K] ⊙ [K] ⊙ x ≡ x
SKK-identˡ = elim
  (λ x → isProp→isSet (SKβ-isSet ([S] ⊙ [K] ⊙ [K] ⊙ x) x))  
  helper 
  (λ a b r → isProp→PathP 
    (λ i → SKβ-isSet 
            ([S] ⊙ [K] ⊙ [K] ⊙ eq/ a b r i) 
            (eq/ a b r i))
            (helper a) (helper b)
  ) _
  where
    helper : ∀ x → [S] ⊙ [K] ⊙ [K] ⊙ [ x ] ≡ [ x ]
    helper x = 
        [S] ⊙ [K] ⊙ [K] ⊙ [ x ] 
      ≡⟨ refl ⟩
        [ S ⋅ K ⋅ K ⋅ x ]
      ≡⟨ eq/ _ _ βS ⟩
        [ K ⋅ x ⋅ (K ⋅ x) ]
      ≡⟨ eq/ _ _ βK ⟩
        [ x ] 
      ∎

is-βnf : SK → Type₀
is-βnf = λ x → ¬ Σ _ (λ y → (x ↝β y))

[_]β : SK → SKβ
[_]β = [_]

S-is-βnf : is-βnf S
S-is-βnf = λ{ (y , ())}

K-is-βnf : is-βnf K
K-is-βnf = λ{ (y , ())}


