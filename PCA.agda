{-# OPTIONS --cubical #-}
module PCA where
open import Level renaming (suc to 𝓁-suc)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe.Properties
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.Data.Nat
open import Cubical.Data.Empty renaming (elim to ⊥-elim)

private
  variable
    𝓁 : Level
    c : Level

record IsPartialMagma {A : Type 𝓁} (_⋅_↓ : A → A → Set c)  (_⋅_ : ∀ (x y : A) → {{_ : x ⋅ y ↓ }} → A) : Type (c ⊔ 𝓁) where
  constructor ispartialmagma
  field
    is-propsition : ∀ {x y} → isProp (x ⋅ y ↓)
    is-set : isSet A

record PartialMagmaStr (A : Type 𝓁) : Type (𝓁-suc 𝓁) where
  constructor partialmagmastr
  field
    _⋅_↓ : A → A → Set 𝓁
    _⋅_ : ∀ x y {{ _ : x ⋅ y ↓ }} → A
    isPartialMagma : IsPartialMagma _⋅_↓ _⋅_

  infixl 7 _⋅_
  infixl 7 _⋅_↓

PartialMagma : Type (𝓁-suc 𝓁)
PartialMagma = TypeWithStr _ PartialMagmaStr

partialmagma : 
    (A : Type 𝓁)
    (_⋅_↓ : A → A → Type 𝓁) 
    (_⋅_ : ∀ x y {{_ : x ⋅ y ↓}} → A )
    (h : IsPartialMagma _⋅_↓ _⋅_) → PartialMagma
partialmagma A _⋅_↓ _⋅_ h = A , partialmagmastr _⋅_↓ _⋅_ h


{-
record IsPCA {A : Type 𝓁} (_⋅?_ : A → A → Maybe A) (k : A) (s : A) : Type 𝓁 where
  constructor ispca
  field
    isPartialMagma : IsPartialMagma _⋅?_

  open PartialMagmaStr (partialmagmastr _⋅?_ isPartialMagma) hiding (_⋅?_)

  field
    {{k-total}} : ∀ {a} → k ⋅ a ↓
    k-const : ∀ {a b} → (k ⋅ a) ⋅? b ≡ just a
    {{s-total₁}} : ∀ {f} → s ⋅ f ↓
    {{s-total₂}} : ∀ {f g} → (s ⋅ f) ⋅ g ↓
    s-starling : ∀ {f g x} → (s ⋅ f ⋅ g) ⋅? x ≡ (f ⋅? x) ⊙ (g ⋅? x)
  

record PCAStr (A : Type 𝓁) : Type (𝓁-suc 𝓁) where
  constructor pcastr
  field
    _⋅?_ : A → A → Maybe A
    k : A
    s : A
    isPCA : IsPCA _⋅?_ k s

  open IsPCA isPCA public
  open PartialMagmaStr (partialmagmastr _⋅?_ isPartialMagma)
    hiding (isPartialMagma ; _⋅?_)
    public
  
  i : A
  i = s ⋅ k ⋅ k

  i-⋅?-identityˡ : ∀ {x} → i ⋅? x ≡ just x
  i-⋅?-identityˡ {x} =
        i ⋅? x 
      ≡⟨ refl ⟩
        (s ⋅ k ⋅ k) ⋅? x
      ≡⟨ s-starling {k} {k} {x} ⟩
        (k ⋅? x) ⊙ (k ⋅? x)
      ≡⟨ cong₂ _⊙_ just-⋅-comm just-⋅-comm ⟩
        just (k ⋅ x) ⊙ just (k ⋅ x)
      ≡⟨ refl ⟩
        (k ⋅ x) ⋅? (k ⋅ x)
      ≡⟨ k-const ⟩
        just x
      ∎

  i-total-inhabited : ∀ {x} → i ⋅ x ↓ ≡ Unit
  i-total-inhabited {x} =
    i ⋅ x ↓ ≡⟨ refl ⟩ is-just (i ⋅? x) ≡⟨ cong is-just i-⋅?-identityˡ ⟩ Unit ∎

  instance    
    i-total : ∀ {x} → i ⋅ x ↓
    i-total {x} = 
      transport (sym (i-total-inhabited {x})) tt

  i-identityˡ : ∀ {x} → i ⋅ x ≡ x
  i-identityˡ {x} = ⋅?-to-⋅ i-⋅?-identityˡ

PCA : Type (𝓁-suc 𝓁)
PCA = TypeWithStr _ PCAStr

pca : (A : Type 𝓁) (_⋅?_ : A → A → Maybe A) (k s : A) (h : IsPCA _⋅?_ k s) → PCA
pca A _⋅?_ k s h = A , pcastr _⋅?_ k s h

data NatType : Set where
  Nat : NatType
  Fn : NatType → NatType -> NatType

fromNatType : NatType → Set
fromNatType Nat = ℕ
fromNatType (Fn dom cod) = fromNatType dom → fromNatType cod

caseNatType : Set  → Set → NatType → Set
caseNatType base _ Nat = base
caseNatType _ fn (Fn _ _) = fn

¬Fn≡Nat : ∀ {a b} → ¬ (Fn a b ≡ Nat)
¬Fn≡Nat {a} {b} pf = subst (caseNatType ⊥ NatType) pf Nat

¬Nat≡Fn : ∀ {a b} → ¬ (Nat ≡ Fn a b)
¬Nat≡Fn {a} {b} pf = subst (caseNatType NatType ⊥) pf Nat

Fn-proj₁-def : NatType → NatType → NatType
Fn-proj₁-def _ (Fn dom _) = dom
Fn-proj₁-def x Nat = x

Fn-proj₂-def : NatType → NatType → NatType
Fn-proj₂-def _ (Fn _ cod) = cod
Fn-proj₂-def x Nat = x

Fn-inj₁ : ∀{a a₁ b b₁} → Fn a b ≡ Fn a₁ b₁ → a ≡ a₁
Fn-inj₁ {a} eq = cong (Fn-proj₁-def a) eq

Fn-inj₂ : ∀{a a₁ b b₁} → Fn a b ≡ Fn a₁ b₁ → b ≡ b₁
Fn-inj₂ {a} eq = cong (Fn-proj₂-def a) eq

_≟T_ : (x y : NatType) → Dec (x ≡ y)
Nat ≟T Nat = yes refl
Fn _ _ ≟T Nat = no ¬Fn≡Nat
Nat ≟T Fn _ _ = no ¬Nat≡Fn
Fn a b ≟T Fn a′ b′ with a ≟T a′ | b ≟T b′
... | yes a≡a′ | yes b≡b′ = yes (cong₂ Fn a≡a′ b≡b′)
... | no ¬a≡a′ | _ = no (λ pf → ⊥-elim (¬a≡a′ (Fn-inj₁ pf)))
... | _ | no ¬b≡b′ = no (λ pf → ⊥-elim (¬b≡b′ (Fn-inj₂ pf)))

instance
  dec-eql-NatType : {x y : NatType} → Dec (x ≡ y)
  dec-eql-NatType {x} {y} = x ≟T y

record HighFunc : Set where
  constructor highfunc
  field
    type : NatType
    impl : fromNatType type

infixl 7 _⋅?ℕ_

_⋅?ℕ_ : HighFunc → HighFunc → Maybe HighFunc
highfunc Nat _ ⋅?ℕ _ = nothing
highfunc (Fn src dst) f ⋅?ℕ highfunc src′ a
  with src′ ≟T src
... | yes eql = just (highfunc dst (f (subst fromNatType eql a)))
... | no _ = nothing
 -}