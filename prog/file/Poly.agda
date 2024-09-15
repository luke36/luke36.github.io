--- encode the type system of the assertion language in VST-IDE

{-# OPTIONS --without-K #-}

module plfa.part2.Poly where

open import Data.List using (List; _∷_; [])
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤?_; z≤n; s≤s)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans)
open import Relation.Nullary using (Dec; yes; no; ¬_; _because_; ofʸ; ofⁿ)
open import Relation.Nullary.Decidable using (True; toWitness)
open import Agda.Builtin.Bool using (true; false)

data Kind : Set where
 ⋆    :  Kind
 _⇛_  :  Kind → Kind → Kind

K⟦_⟧ : Kind → Set₁
K⟦ ⋆ ⟧     = Set
K⟦ j ⇛ k ⟧ = K⟦ j ⟧ → K⟦ k ⟧

infixl 5  _,_

data TypeContext : Set where
  ∅   : TypeContext
  _,_ : TypeContext → Kind → TypeContext

infix  4  _∋T_
infix  9  S_

data _∋T_ : TypeContext → Kind → Set where

  Z : ∀ {Γ A}
        ------------
      → Γ , A ∋T A

  S_ : ∀ {Γ A B}
     → Γ ∋T A
       ------------
     → Γ , B ∋T A

infixr 7  _⇒_
infixl 8  _∘_
infix  9  ``_

infix  4  _⊩_

data _⊩_ (Γ : TypeContext) : Kind → Set where
  ``_  :  ∀ {k} → (Γ ∋T k) → Γ ⊩ k
  _∘_  :  ∀ {j k} → Γ ⊩ j ⇛ k → Γ ⊩ j → Γ ⊩ k
  _⇒_  :  Γ ⊩ ⋆ → Γ ⊩ ⋆ → Γ ⊩ ⋆

TypeEnv : TypeContext → Set₁
TypeEnv Γ = ∀ {k} (t : Γ ∋T k) → K⟦ k ⟧

infixl 5  _`,T_

`∅T : TypeEnv ∅
`∅T ()

_`,T_ : ∀ {Γ k} → TypeEnv Γ → K⟦ k ⟧ → TypeEnv (Γ , k)
(γ `,T v) Z     = v
(γ `,T v) (S x) = γ x

T⟦_⟧ : ∀ {Γ k} → Γ ⊩ k → TypeEnv Γ → K⟦ k ⟧
T⟦ `` x ⟧ γ  = γ x
T⟦ a ∘ b ⟧ γ = (T⟦ a ⟧ γ) (T⟦ b ⟧ γ)
T⟦ a ⇒ b ⟧ γ = T⟦ a ⟧ γ → T⟦ b ⟧ γ

infixl 5  _⨟T_

_⨟T_ : TypeContext → TypeContext → TypeContext
Γ ⨟T ∅       = Γ
Γ ⨟T (Δ , A) = (Γ ⨟T Δ) , A

--- type scheme
infix  4  _⊩Δ_

data _⊩Δ_ (Γ : TypeContext) (K : Kind) : Set where
  [_&_] : (Δ : TypeContext) → Γ ⨟T Δ ⊩ K → Γ ⊩Δ K

data Context (Γ : TypeContext) : Set where
  ∅    : Context Γ
  _,_  : Context Γ → Γ ⊩Δ ⋆ → Context Γ

infix  4 _∋_

data _∋_ {Γ : TypeContext} : Context Γ → Γ ⊩Δ ⋆ → Set where

  Z : ∀ {Δ A}
      ------------------
    → Δ , A ∋ A

  S_ : ∀ {Δ A B}
     → Δ ∋ A
       ------------------
     → Δ , B ∋ A

subst : ∀ {Γ Δ}
  → (∀ {K} → Γ ∋T K → Δ ⊩ K)
  → (∀ {K} → Γ ⊩ K → Δ ⊩ K)
subst σ (`` x)  = σ x
subst σ (t ∘ s) = (subst σ t) ∘ (subst σ s)
subst σ (s ⇒ t) = (subst σ s) ⇒ (subst σ t)

data SeparateContextCase (K : Kind) (Γ Δ : TypeContext) : Set where
  in-Γ : Γ ∋T K → SeparateContextCase K Γ Δ
  in-Δ : Δ ∋T K → SeparateContextCase K Γ Δ

separateContext : ∀ {K} (Γ Δ : TypeContext)
  → (In : Γ ⨟T Δ ∋T K) → SeparateContextCase K Γ Δ
separateContext Γ ∅ p       = in-Γ p
separateContext Γ (Δ , K) Z = in-Δ Z
separateContext Γ (Δ , K) (S n) with separateContext Γ Δ n
... | in-Γ p = in-Γ p
... | in-Δ q = in-Δ (S q)

infixl 5  _`⨟T_

_`⨟T_ : ∀ {Γ Δ}
  → TypeEnv Γ
  → TypeEnv Δ
    ---------------------
  → TypeEnv (Γ ⨟T Δ)
(γ `⨟T δ) x with separateContext _ _ x
... | in-Γ p = γ p
... | in-Δ q = δ q

lift : ∀ {Γ Δ}
  → (∀ {K} → Δ ∋T K → Γ ⊩ K)
  → (∀ {K} → Γ ⨟T Δ ∋T K → Γ ⊩ K)
lift {Γ} {Δ} σ p with separateContext Γ Δ p
... | in-Γ p = `` p
... | in-Δ q = σ q

data Instantiate (Γ : TypeContext) : TypeContext → Set where
  ∅   : Instantiate Γ ∅
  _,_ : ∀ {Δ} {K} → Instantiate Γ Δ → Γ ⊩ K → Instantiate Γ (Δ , K)

doInstantiate : ∀ {Γ Δ}
  → Instantiate Γ Δ
  → ∀ {K} → Δ ∋T K → Γ ⊩ K
doInstantiate (σ , K) Z     = K
doInstantiate (σ , K) (S n) = doInstantiate σ n

substParameter : ∀ {Γ Δ}
  → (Instantiate Γ Δ)
  → (∀ {K} → Γ ⨟T Δ ⊩ K → Γ ⊩ K)
substParameter σ t = subst (lift (doInstantiate σ)) t

infix  4  _⊢_

infixl 7  _∙_
infix  9  `_∙_

data _⊢_ {Γ : TypeContext} (Δ : Context Γ) : Γ ⊩ ⋆ → Set where
  `_∙_  : ∀ {Γ' : TypeContext} {T}
        → (p : Δ ∋ [ Γ' & T ])
        → (σ : Instantiate Γ Γ')
          ------------
        → Δ ⊢ substParameter σ T
  _∙_ : ∀ {a b}
        → Δ ⊢ a ⇒ b
        → Δ ⊢ a
          ------------
        → Δ ⊢ b

Env : ∀ {Γ} → TypeEnv Γ → Context Γ → Set₁
Env γ Γ = ∀ {Δ t} (x : Γ ∋ [ Δ & t ])
          → ((δ : TypeEnv Δ)
             → T⟦ t ⟧ (γ `⨟T δ))

infixl 5  _`,_

`∅ : ∀ {Γ} {γ : TypeEnv Γ} → Env γ ∅
`∅ ()

_`,_ : ∀ {Γ Γ' T} {Δ : Context Γ} {γ : TypeEnv Γ}
       → Env γ Δ → ((δ : TypeEnv Γ') → T⟦ T ⟧ (γ `⨟T δ)) → Env γ (Δ , [ Γ' & T ])
(γ `, v) Z     = v
(γ `, v) (S x) = γ x

instantiationDenote : ∀ {Γ Δ}
  → TypeEnv Γ
  → Instantiate Γ Δ
    ------------------
  → TypeEnv Δ
instantiationDenote γ (σ , x) Z     = T⟦ x ⟧ γ
instantiationDenote γ (σ , _) (S x) = instantiationDenote γ σ x 

instantiate-correct : ∀ {Γ Δ K}
  → (x : Δ ∋T K) → (σ : Instantiate Γ Δ) → (γ : TypeEnv Γ)
  → T⟦ doInstantiate σ x ⟧ γ
  ≡ instantiationDenote γ σ x
instantiate-correct {Γ} {.(_ , _)} Z (σ , x) γ = refl
instantiate-correct {Γ} {.(_ , _)} (S x) (σ , x₁) γ = instantiate-correct x σ γ

subst-correct : ∀ {Γ Δ K}
  → (σ : Instantiate Γ Δ) → (T : Γ ⨟T Δ ⊩ K) → (γ : TypeEnv Γ)
    ------------
  → T⟦ substParameter σ T ⟧ γ
  ≡ T⟦ T ⟧ (γ `⨟T instantiationDenote γ σ)
subst-correct {Γ} {Δ} σ (`` x) γ with separateContext Γ Δ x
... | in-Γ p = refl
... | in-Δ q = instantiate-correct q σ γ
subst-correct σ (t ∘ s) E
  rewrite (subst-correct σ t E) rewrite (subst-correct σ s E) = refl
subst-correct σ (t ⇒ s) E
  rewrite (subst-correct σ t E) rewrite (subst-correct σ s E) = refl

termIdDenote : ∀ {Γ Γ'} {γ : TypeEnv Γ} {Δ : Context Γ} {T}
  → (Δ ∋ [ Γ' & T ])
  → (σ : Instantiate Γ Γ')
  → Env γ Δ → T⟦ substParameter σ T ⟧ γ
termIdDenote {Γ} {Γ'} {γ} {Δ} {T} x σ δ
  rewrite subst-correct σ T γ = δ x (instantiationDenote γ σ)

⟦_⟧ : ∀ {Γ T} {γ : TypeEnv Γ} {Δ : Context Γ}
  → Δ ⊢ T
  → Env γ Δ
  → T⟦ T ⟧ γ
⟦ ` x ∙ σ ⟧ = termIdDenote x σ
⟦ a ∙ b ⟧ γ = (⟦ a ⟧ γ) (⟦ b ⟧ γ)

--- test

length-T : TypeContext → ℕ
length-T ∅        =  zero
length-T (Γ , _)  =  suc (length-T Γ)

length : ∀ {Γ} → Context Γ → ℕ
length ∅        =  zero
length (Γ , _)  =  suc (length Γ)

count-T : ∀ {Γ} → {n : ℕ} → (p : n < length-T Γ) → Σ[ K ∈ Kind ] (Γ ∋T K)
count-T {Γ , K} {zero} (s≤s z≤n)  =  ⟨ K , Z ⟩ 
count-T {Γ , _} {(suc n)} (s≤s p) with count-T p
...                                  | ⟨ K , n ⟩ = ⟨ K , S n ⟩

count : ∀ {Γ Δ} → {n : ℕ} → (p : n < length Δ) → Σ[ T ∈ Γ ⊩Δ ⋆ ] (Δ ∋ T)
count {Γ} {Δ , T} {zero} (s≤s z≤n)  =  ⟨ T , Z ⟩ 
count {Γ} {Δ , _} {(suc n)} (s≤s p) with count p
...                                    | ⟨ T , n ⟩ = ⟨ T , S n ⟩

#T_ : ∀ {Γ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length-T Γ)}
      --------------------------------
    → Γ ⊩ proj₁ (count-T (toWitness n∈Γ))
#T_ n {n∈Γ} = `` proj₂ (count-T (toWitness n∈Γ))

#-help : ∀ {Γ Δ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length Δ)}
      --------------------------------
    → Σ[ Γ' ∈ TypeContext ] (
      Σ[ B  ∈ Γ ⨟T Γ' ⊩ ⋆ ] (
        (σ : Instantiate Γ Γ')
      → Δ ⊢ substParameter σ B))
#-help n {n∈Γ} with count (toWitness n∈Γ)
...                 | ⟨ [ Δ & T ] , x ⟩ = ⟨ Δ , ⟨ T , `_∙_ x ⟩ ⟩

# : ∀ {Γ Δ}
    → (n : ℕ)
    → {n∈Γ : True (suc n ≤? length Δ)}
      ------------
    → (σ : Instantiate Γ (proj₁ (#-help {Γ} {Δ} n {n∈Γ})))
    → Δ ⊢ substParameter σ (proj₁ (proj₂ (#-help {Γ} {Δ} n)))
# n = proj₂ (proj₂ (#-help n))

Γ : TypeContext
Γ = ∅ , ⋆
      , ⋆ ⇛ ⋆

Δ : Context Γ
Δ = ∅ , [ ∅ & #T 1 ]
      , [ ∅ & #T 1 ⇒ #T 1 ]
      , [ ∅ , ⋆ & #T 1 ∘ #T 0 ]
      , [ ∅ , ⋆ & #T 0 ⇒ #T 1 ∘ #T 0 ⇒ #T 1 ∘ #T 0 ]
      , [ ∅ , ⋆ & #T 0 ⇒ #T 1 ∘ #T 0 ⇒ #T 0 ]

T⟦⟧ : TypeEnv Γ
T⟦⟧ = `∅T `,T ℕ
          `,T List

⟦⟧ : Env T⟦⟧ Δ
⟦⟧ = `∅ `, (λ { `∅ → zero })
        `, (λ { `∅ → suc })
        `, (λ { _ → [] })
        `, (λ { _ → _∷_ })
        `, (λ { _ → λ { x [] → x ; x (y ∷ l) → y} })

_ : ⟦ # 0 (∅ , #T 1) ∙
        (# 3 ∅ ∙ # 4 ∅) ∙
        (# 1 (∅ , #T 1) ∙ # 4 ∅ ∙ # 2 (∅ , #T 1)) ⟧ ⟦⟧ ≡ zero
_ = refl

_ : ∀ {t d e l}
  → ⟦ # 0 (∅ , t) ∙ d ∙ (# 1 (∅ , t) ∙ e ∙ l) ⟧ ⟦⟧
  ≡ ⟦ e ⟧ ⟦⟧
_ = refl

extRight : ∀ {Γ A} → (K : Kind) → (Γ ⊩ A) → (Γ , K ⊩ A)
extRight _ (`` x)   = `` S x
extRight _ (t ∘ t₁) = extRight _ t ∘ extRight _ t₁
extRight _ (t ⇒ t₁) = extRight _ t ⇒ extRight _ t₁

ext-right-correct : ∀ {Γ A K}
  → (E : TypeEnv Γ) → (⟦K⟧ : K⟦ K ⟧)
  → (t : Γ ⊩ A)
    ------------
  → T⟦ t ⟧ E ≡ T⟦ extRight K t ⟧ (E `,T ⟦K⟧)
ext-right-correct E ⟦K⟧ (`` x) = refl
ext-right-correct E ⟦K⟧ (t ∘ t₁)
 rewrite ext-right-correct E ⟦K⟧ t
 rewrite ext-right-correct E ⟦K⟧ t₁ = refl
ext-right-correct E ⟦K⟧ (t ⇒ t₁)
 rewrite ext-right-correct E ⟦K⟧ t
 rewrite ext-right-correct E ⟦K⟧ t₁ = refl

extsRight : ∀ {Γ A} → (Δ : TypeContext) → (Γ ⊩ A) → (Γ ⨟T Δ ⊩ A)
extsRight ∅ t       = t
extsRight (Δ , x) t = extRight x (extsRight Δ t)

exts-right-correct : ∀ {Γ Δ A}
  → (E : TypeEnv Γ) → (F : TypeEnv Δ)
  → (t : Γ ⊩ A)
    ------------
  → T⟦ t ⟧ E ≡ T⟦ extsRight Δ t ⟧ (E `⨟T F)
exts-right-correct {Γ} {∅} E T t = refl
exts-right-correct {Γ} {Δ₁ , x} E T t
  = trans (exts-right-correct E (λ x → T (S x)) t) {!ext-right-correct E ? !}

-- extTypeScheme : ∀ Γ Δ → {A : Kind} → (K : Kind) → (Γ ⍮T Δ ⊩ A) → ((Γ , K) ⍮T Δ ⊩ A)
-- extTypeScheme Γ Δ K (`` x) with separateContext Γ Δ x
-- ... | in-Γ p = extsRight Δ (`` S p)
-- ... | in-Δ Z = `` Z
-- extTypeScheme Γ .(_ , _) K (`` Z) | in-Δ (S_ {B = _} q) = `` Z
-- extTypeScheme Γ .(_ , B) K (`` (S x)) | in-Δ (S_ {B = B} q) = extRight B (extTypeScheme Γ _ K (`` x))
-- extTypeScheme _ _ K (t ∘ t₁) = extTypeScheme _ _ K t ∘ extTypeScheme _ _ K t₁
-- extTypeScheme _ _ K (t ⇒ t₁) = extTypeScheme _ _ K t ⇒ extTypeScheme _ _ K t₁

-- ext-scheme-correct : ∀ {Γ Δ K A}
--   → (E : TypeContextDenote Γ) → (F : TypeContextDenote Δ) → (⟦K⟧ : K⟦ K ⟧)
--   → (t : Γ ⍮T Δ ⊩ A)
--     ------------
--   → T⟦ t In E ⨟T F ⟧ ≡
--     T⟦ extTypeScheme Γ Δ K t In (E , ⟦K⟧) ⨟T F ⟧
-- ext-scheme-correct {Γ} {Δ} E F ⟦K⟧ (`` x) with separateContext Γ Δ x in eq
-- ... | in-Γ p = trans (trans (separate-correct E F x) triv)
--                      (exts-right-correct (E , ⟦K⟧) F (`` S p))
--                where
--                  triv : separateContextDenote E F (separateContext Γ Δ x) ≡ typeIdDenote p E
--                  triv rewrite eq = refl
-- ext-scheme-correct {Γ} {Δ , y} E (F , V) ⟦K⟧ (`` x) | in-Δ Z =
--   trans (separate-correct E (F , V) x) triv
--   where
--     triv : separateContextDenote E (F , V) (separateContext Γ (Δ , y) x) ≡ typeIdDenote Z (F , V)
--     triv rewrite eq = refl
-- ext-scheme-correct {Γ} {Δ , y} E (F , V) ⟦K⟧ (`` (S x)) | in-Δ (S q) =
--   trans (ext-scheme-correct E F ⟦K⟧ (`` x))
--         (ext-right-correct ((E , ⟦K⟧) ⨟T F) V
--                               (extTypeScheme Γ _ _ (`` x)) )
-- ext-scheme-correct {Γ} {Δ} E F ⟦K⟧ (a ∘ b)
--   rewrite ext-scheme-correct E F ⟦K⟧ a
--   rewrite ext-scheme-correct E F ⟦K⟧ b = refl
-- ext-scheme-correct {Γ} {Δ} E F ⟦K⟧ (a ⇒ b)
--   rewrite ext-scheme-correct E F ⟦K⟧ a
--   rewrite ext-scheme-correct E F ⟦K⟧ b = refl

-- extContext : ∀ {Γ} → (K : Kind) → Context Γ → Context (Γ , K)
-- extContext _ ∅                    = ∅
-- extContext {Γ} K (Δ , [ Γ' & B ]) = extContext K Δ , [ Γ' & extTypeScheme Γ Γ' K B ]

-- extTerm : ∀ {Γ Δ B} → (A : Γ ⊩Δ ⋆) → (Δ ⊢ B) → (Δ , A ⊢ B)
-- extTerm A (` p ∙ σ) = ` S p ∙ σ
-- extTerm A (t ∙ t₁)  = extTerm A t ∙ extTerm A t₁

-- extContextDenote : ∀ {Γ} → {Δ : Context Γ}
--   → {T⟦⟧ : TypeContextDenote Γ}
--   → (K : Kind) → (⟦K⟧ : K⟦ K ⟧)
--   → (⟦⟧ : ContextDenote T⟦⟧ Δ)
--     ------------
--   → ContextDenote (T⟦⟧ , ⟦K⟧) (extContext K Δ)
-- extContextDenote {Γ} {∅} {T⟦⟧} K ⟦K⟧ ⟦⟧ = ∅
-- extContextDenote {Γ} {Δ , [ Γ' & T ]} {T⟦⟧} K ⟦K⟧ (⟦⟧ , x) =
--   extContextDenote K ⟦K⟧ ⟦⟧ , λ { F → change (ext-scheme-correct T⟦⟧ F ⟦K⟧ T) (x F) }
--   where
--     change : ∀ {A B : Set} → (A ≡ B) → A → B
--     change refl a = a

-- _ : ∀ {A : Set} {a : A}
--     → let ⟦⟧' = (extContextDenote ⋆ A ⟦⟧) , (λ { ∅ → a }) in
--       ⟦ # 1 (∅ , #T 0) ∙ # 0 ∅ ∙
--           (# 2 (∅ , #T 0) ∙ # 0 ∅ ∙ # 3 (∅ , #T 0)) In ⟦⟧' ⟧
--     ≡ a
-- _ = refl

-- infixl 5  _⍮_

-- _⍮_ : ∀ {Γ : TypeContext} → Context Γ → Context Γ → Context Γ
-- Γ ⍮ ∅       = Γ
-- Γ ⍮ (Δ , A) = (Γ ⍮ Δ) , A

-- _⨟_ : ∀ {T : TypeContext} {E : TypeContextDenote T}
--         {Γ Δ : Context T}
--   → ContextDenote E Γ
--   → ContextDenote E Δ
--     ---------------------
--   → ContextDenote E (Γ ⍮ Δ)
-- V ⨟ ∅       = V
-- V ⨟ (W , v) = (V ⨟ W) , v

-- infix  6  _:=_

-- data Command {T : TypeContext} (Γ : Context T) (Δ : Context T) : Set where
--   _:=_ : ∀ {t} → Δ ∋ [ ∅ & t ] → Γ ⍮ Δ ⊢ t → Command Γ Δ
--   _,_  : Command Γ Δ → Command Γ Δ → Command Γ Δ

-- data Program {T : TypeContext} (Γ : Context T) : Set where
--   Declare_In_ : (Δ : Context T) → Command Γ Δ → Program Γ

-- updateContext : ∀ {T : TypeContext} {E : TypeContextDenote T}
--                   {Δ : Context T} {t}
--                 → ContextDenote E Δ
--                 → Δ ∋ [ ∅ & t ] → (v : T⟦ t In E ⟧)
--                 → ContextDenote E Δ
-- updateContext (V , v) Z w     = V , λ { ∅ → w }
-- updateContext (V , v) (S x) w = updateContext V x w , v

-- data CommandDenote {T : TypeContext} {E : TypeContextDenote T}
--                    (Γ : Context T) (C : ContextDenote E Γ) (Δ : Context T)
--   : Command Γ Δ → ContextDenote E Δ → ContextDenote E Δ → Set₁ where
--   ⟦_:=_⟧ : ∀ {V t} → (x : Δ ∋ [ ∅ & t ]) → ∀ w → CommandDenote Γ C Δ
--                (x := w) V (updateContext V x ⟦ w In C ⨟ V ⟧)
--   ⟦_,_⟧  : ∀ {U V W c d}
--           → CommandDenote Γ C Δ c V W
--           → CommandDenote Γ C Δ d W U
--             ------------
--           → CommandDenote Γ C Δ (c , d) V U


