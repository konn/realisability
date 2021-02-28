{-# OPTIONS --cubical #-}
module PCA where
open import Level renaming (suc to 𝓁-suc ; _⊔_ to _⊔𝓁_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Maybe
open import Cubical.Data.Maybe.Properties
open import Cubical.Foundations.Structure
open import Cubical.Relation.Nullary
open import Cubical.Data.Unit
open import Cubical.Data.Sum
open import Cubical.Data.Prod
open import Cubical.Data.Empty
open import Cubical.Data.Nat
open import Cubical.Data.Empty renaming (elim to ⊥-elim)

private
  variable
    𝓁 : Level
    c : Level

record IsPartialMagma {A : Type 𝓁} (_⋅_↓ : A → A → Set c)  (_⋅_ : ∀ (x y : A) → {{_ : x ⋅ y ↓ }} → A) : Type (c ⊔𝓁 𝓁) where
  constructor ispartialmagma
  field
    ↓-isProp : ∀ {x y} → isProp (x ⋅ y ↓)
    carrier-isSet : isSet A

record PartialMagmaStr (A : Type 𝓁) : Type (𝓁-suc 𝓁) where
  constructor partialmagmastr
  field
    _⋅_↓ : A → A → Set 𝓁
    _⋅_ : ∀ x y {{ _ : x ⋅ y ↓ }} → A
    isPartialMagma : IsPartialMagma _⋅_↓ _⋅_

  infixl 7 _⋅_
  infix 7 _⋅_↓

PartialMagma : Type (𝓁-suc 𝓁)
PartialMagma = TypeWithStr _ PartialMagmaStr

partialmagma : 
    (A : Type 𝓁)
    (_⋅_↓ : A → A → Type 𝓁) 
    (_⋅_ : ∀ x y {{_ : x ⋅ y ↓}} → A )
    (h : IsPartialMagma _⋅_↓ _⋅_) → PartialMagma
partialmagma A _⋅_↓ _⋅_ h = A , partialmagmastr _⋅_↓ _⋅_ h

cong₃ : ∀ {A : Type 𝓁} {B : A → Type 𝓁} {C : (a : A) → B a → Type 𝓁 }
        {D : (a : A) → (b : B a) → (c : C a b) → Type 𝓁} →
        (f : (a : A) → (b : B a) → (c : C a b) → D a b c) →
        {x y : A} → 
        (p : x ≡ y) →
        {u : B x} {v : B y}
        (q : PathP (λ i → B (p i)) u v) →
        {α : C x u} {β : C y v} → 
        (r : PathP (λ i → C (p i) (q i)) α β) →
        PathP (λ i → D (p i) (q i) (r i)) (f x u α) (f y v β)
cong₃ f p q r i = f (p i) (q i) (r i)

module TermSyntax {𝓁} (M : PartialMagma {𝓁}) where
  open PartialMagmaStr (snd M)
  open IsPartialMagma isPartialMagma using (↓-isProp ; carrier-isSet)
  data ClosedTerm : Type 𝓁 where
    ⟦_⟧ : fst M → ClosedTerm
    _⊙_ : ClosedTerm → ClosedTerm → ClosedTerm

  data _⇓_ : ClosedTerm → fst M →  Type 𝓁 where
    ⟦⟧⇓ : ∀ {t} → ⟦ t ⟧ ⇓ t
    ⊙⇓ : ∀ {x y t u} → x ⇓ t → y ⇓ u → {{_ : t ⋅ u ↓}} → (x ⊙ y) ⇓ (t ⋅ u)

  infixl 7 _⊙_
  infix 6 _⇓ _⇓_


  _⇓ : ClosedTerm → Type 𝓁
  x ⇓ = Σ _ (x ⇓_)

  ⇓-injʳ : ∀ {x t u} → x ⇓ t → x ⇓ u → t ≡ u
  ⇓-injʳ {.(⟦ t ⟧)} {t} {.t} ⟦⟧⇓ ⟦⟧⇓ = refl
  ⇓-injʳ {.(x ⊙ y)} {.(t ⋅ u)} {.(t′ ⋅ u′)} 
    (⊙⇓ {x} {y} {t} {u} x⇓t y⇓u {{t⋅u↓}}) 
    (⊙⇓ {.x} {.y} {t′} {u′} x⇓t′ y⇓u′ {{t′⋅u′↓}}) = 
      _⋅_ t u {{t⋅u↓}}
    ≡⟨ cong₃
        (λ x y z → (x ⋅ y) ⦃ z ⦄) 
        (⇓-injʳ x⇓t x⇓t′) (⇓-injʳ y⇓u y⇓u′) 
        (transport-filler cong-↓ t⋅u↓)
    ⟩
      _⋅_ t′ u′ {{transport cong-↓ t⋅u↓}}
    ≡⟨ cong (λ z → _⋅_ t′ u′ {{z}}) (↓-isProp _ _)  ⟩
      _⋅_ t′ u′ ⦃ t′⋅u′↓ ⦄
    ∎
    where
      cong-↓ = cong₂ _⋅_↓ (⇓-injʳ x⇓t x⇓t′) (⇓-injʳ y⇓u y⇓u′)

  private
    ⇓-isProp-aux-prop
      : ∀ {x t} → (p : x ⇓ t) → (q : x ⇓ t)
      → ⇓-injʳ p q ≡ refl
    ⇓-isProp-aux-prop {x} {t} p q =
      carrier-isSet t t (⇓-injʳ p q) refl

    ⇓-isProp-aux₀
      : ∀ {x t u} → (p : x ⇓ t) → (q : x ⇓ u)
      → transport (cong (x ⇓_) (⇓-injʳ p q)) p ≡ q
    ⇓-isProp-aux₀ {.(⟦ t ⟧)} {t} {.t} (⟦⟧⇓ {t}) (⟦⟧⇓ {t}) =
        transport (λ i → ⟦ t ⟧ ⇓ ⇓-injʳ (⟦⟧⇓ {t}) (⟦⟧⇓ {t}) i) (⟦⟧⇓ {t})
      ≡⟨ cong 
          (λ pf → transport (cong (⟦ t ⟧ ⇓_) pf) (⟦⟧⇓ {t})) 
          (⇓-isProp-aux-prop (⟦⟧⇓ {t}) (⟦⟧⇓ {t}))
        ⟩
        transport refl (⟦⟧⇓ {t})
      ≡⟨ transportRefl ⟦⟧⇓ ⟩
        ⟦⟧⇓ {t}
      ∎
    ⇓-isProp-aux₀ {(t ⊙ u)} {.(l ⋅ r)} {.(_ ⋅ _)} 
      (⊙⇓ {t} {u} {l} {r} t⇓l u⇓r ⦃ l⋅r↓ ⦄)
      (⊙⇓ {t} {u} {l′} {r′} t⇓l′ u⇓r′ ⦃ l′⋅r′↓ ⦄) =
          transport 
            (cong ((t ⊙ u) ⇓_) (⇓-injʳ p q))
            p
        ≡⟨ cong₃
            (λ _ x y →  
              transport 
                  (cong (t ⊙ u ⇓_) (⇓-injʳ ((⊙⇓ x  u⇓r ⦃ y ⦄)) q))  
                  (⊙⇓ x  u⇓r ⦃ y ⦄)
            ) 
            l≡l′ (transport-filler (cong (t ⇓_) l≡l′) t⇓l) 
                (transport-filler (cong (_⋅ r ↓) l≡l′) l⋅r↓)
          ⟩
          transport 
            (cong ((t ⊙ u) ⇓_) (⇓-injʳ pl′ q))
            pl′
        ≡⟨ cong₃
              (λ _ x₁ y →
                transport (cong ((t ⊙ u) ⇓_) (⇓-injʳ (⊙⇓ t⇓trans-l x₁ ⦃ y ⦄) q))
                (⊙⇓ t⇓trans-l x₁ ⦃ y ⦄))
                r≡r′
                (transport-filler (cong (u ⇓_) r≡r′) u⇓r)
                (transport-filler (cong (l′ ⋅_↓) r≡r′) trans-l⋅r↓)
          ⟩
        transport 
            (cong ((t ⊙ u) ⇓_) (⇓-injʳ ptrans q))
            ptrans
        ≡⟨ cong₃
            (λ x y z → transport 
                (cong ((t ⊙ u) ⇓_) (⇓-injʳ (⊙⇓ x y ⦃ z ⦄) q))
                (⊙⇓ x y ⦃ z ⦄)
            ) 
            (t⇓l≡t⇓l′)
            (u⇓r≡u⇓r′)
            (↓-isProp _ l′⋅r′↓)
          ⟩
          transport (cong (t ⊙ u ⇓_) (⇓-injʳ q q))
            (⊙⇓ t⇓l′ u⇓r′ ⦃ l′⋅r′↓ ⦄)
        ≡⟨ cong (λ pf → transport (cong ((t ⊙ u) ⇓_) pf) q) 
            (carrier-isSet (l′ ⋅ r′) (l′ ⋅ r′) (⇓-injʳ q q) refl)
          ⟩
          transport (cong (t ⊙ u ⇓_) refl)
            (⊙⇓ t⇓l′ u⇓r′ ⦃ l′⋅r′↓ ⦄)
        ≡⟨ transportRefl _ ⟩
            ⊙⇓ t⇓l′ u⇓r′ ⦃ l′⋅r′↓ ⦄
        ∎
        where
          -- transf t⇓ u⇓ ↓ = ⊙⇓ t⇓ u⇓ ⦃ ↓ ⦄
          x = t ⊙ u
          l≡l′ = ⇓-injʳ t⇓l t⇓l′
          r≡r′ = ⇓-injʳ u⇓r u⇓r′
          p = ⊙⇓ t⇓l u⇓r ⦃ l⋅r↓ ⦄
          q = ⊙⇓ t⇓l′ u⇓r′ ⦃ l′⋅r′↓ ⦄
          l⋅r≡l′⋅r′ = ⇓-injʳ p q
          l⋅r↓≡l′⋅r′↓ = cong₂ _⋅_↓ l≡l′ r≡r′
          p′ = ⊙⇓ t⇓l′ u⇓r′ ⦃ transport l⋅r↓≡l′⋅r′↓ l⋅r↓ ⦄
          t⇓l≡t⇓l′ = ⇓-isProp-aux₀ t⇓l t⇓l′
          u⇓r≡u⇓r′ = ⇓-isProp-aux₀ u⇓r u⇓r′
          t⇓trans-l = transport (cong (t ⇓_) l≡l′) t⇓l
          trans-l⋅r↓ = transport (cong (_⋅ r ↓) l≡l′) l⋅r↓
          pl′ = ⊙⇓ t⇓trans-l u⇓r 
                  ⦃ trans-l⋅r↓ ⦄
          ptrans = ⊙⇓ 
            (transport (cong (t ⇓_) l≡l′) t⇓l) 
            (transport (cong (u ⇓_) r≡r′) u⇓r)
            ⦃ transport (cong (l′ ⋅_↓) r≡r′) trans-l⋅r↓ ⦄
    
  ⇓-isProp₂
    : ∀ {x t} → (p : x ⇓ t) → (q : x ⇓ t)
    → p ≡ q
  ⇓-isProp₂ {x} {t} p q =
      p
    ≡⟨ sym (transportRefl p) ⟩
      transport (λ i → x ⇓ refl {x = t} i) p
    ≡⟨ cong (λ t≡t → transport (λ i →  x ⇓ t≡t i) p) (sym (⇓-isProp-aux-prop p q)) ⟩
      transport (λ i → x ⇓ ⇓-injʳ p q i) p
    ≡⟨ ⇓-isProp-aux₀ p q ⟩
      q
    ∎
      

  ⇓-isProp₁ : ∀{x} → isProp (x ⇓)
  ⇓-isProp₁ {x} (t , x⇓t) (u , x⇓u) =
      (t , x⇓t)
    ≡⟨ cong₂ {C = λ  _ _ → x ⇓} _,_ t≡u (transport-filler x⇓t≡u x⇓t) ⟩
      (u , transport x⇓t≡u x⇓t)
    ≡⟨ cong {B = λ _ → x ⇓} (u ,_) (⇓-isProp₂ _ x⇓u) ⟩
      (u , x⇓u)
    ∎
    where
      t≡u = ⇓-injʳ x⇓t x⇓u
      x⇓t≡u = cong (x ⇓_) t≡u

  _≃_ : ClosedTerm → ClosedTerm → Type 𝓁
  l ≃ r =
    (∀ {x} → l ⇓ x → r ⇓ x) 
      ×
    (∀ {x} → r ⇓ x → l ⇓ x)

  infix 6 _≃_

  ≃-¬l⇓⇒¬r⇓ : ∀{l r} → l ≃ r → ¬ (l ⇓) → ¬ (r ⇓)
  ≃-¬l⇓⇒¬r⇓ (_ , r⇓⇒l⇓) ¬l⇓ (x , r⇓x) = ¬l⇓ (x , r⇓⇒l⇓ r⇓x)

  ≃-¬r⇓⇒¬l⇓ : ∀{l r} → l ≃ r → ¬ (r ⇓) → ¬ (l ⇓)
  ≃-¬r⇓⇒¬l⇓ (l⇓⇒r⇓ , _) ¬r⇓ (x , l⇓x) = ¬r⇓ (x , l⇓⇒r⇓ l⇓x)

record IsPCA {A : Type 𝓁} (_⋅_↓ : A → A → Type 𝓁) (_⋅_ : (x y : A) → {{_ : x ⋅ y ↓}} → A) (k : A) (s : A) : Type 𝓁 where
  constructor ispca
  field
    isPartialMagma : IsPartialMagma _⋅_↓ _⋅_

  open TermSyntax (partialmagma A _⋅_↓ _⋅_ isPartialMagma)

  field
    {{k-total₁}} : ∀ {a} → k ⋅ a ↓
    {{k-total₂}} : ∀ {a b} → (k ⋅ a) ⋅ b ↓
    k-const : ∀ {a b} → (k ⋅ a) ⋅ b ≡ a
    {{s-total₁}} : ∀ {f} → s ⋅ f ↓
    {{s-total₂}} : ∀ {f g} → (s ⋅ f) ⋅ g ↓
    s-equivalent : ∀ {f g x} → 
      ⟦ s ⟧ ⊙ ⟦ f ⟧ ⊙ ⟦ g ⟧ ⊙ ⟦ x ⟧ ≃
        ⟦ f ⟧ ⊙ ⟦ x ⟧ ⊙ (⟦ g ⟧ ⊙ ⟦ x ⟧)
{-

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