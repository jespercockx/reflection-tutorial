
open import Prelude hiding (_>>=_) renaming (_>>=′_ to _>>=_)
open import Container.List
open import Container.Traversable
open import Tactic.Reflection
open import Tactic.Deriving.Eq

module _ where

module PreludeExtras where

  raise : ∀ {m} n → Fin m → Fin (n +N m)
  raise zero    i = i
  raise (suc n) i = suc (raise n i)

  inject : ∀ {m} n → Fin m → Fin (m +N n)
  inject n zero    = zero
  inject n (suc i) = suc (inject n i)

  module _ {a} {A : Set a} {{_ : Eq A}} where

    findIndex : ∀ {n} → Vec A n → A → Maybe (Fin n)
    findIndex [] a = nothing
    findIndex (x ∷ xs) a = case (x == a) of λ where
      (yes _) → just zero
      (no _ ) → suc <$> findIndex xs a

open PreludeExtras


data P (n : Nat) : Set where
  `⊤   : P n
  `⊥   : P n
  _`∧_ : P n → P n → P n
  _`∨_ : P n → P n → P n
  _`⇒_ : P n → P n → P n
  ??   : Fin n → P n

unquoteDecl eqP = deriveEq eqP (quote P)

Ctx : Nat → Set
Ctx n = List (P n)

data _⊢_ {n : Nat} (Γ : Ctx n) : P n → Set where
  var : ∀ {X} → X ∈ Γ → Γ ⊢ X
  lam : ∀ {X Y} → (X ∷ Γ) ⊢ Y → Γ ⊢ (X `⇒ Y)
  tt  : Γ ⊢ `⊤
  _,_ : ∀ {X Y} → Γ ⊢ X → Γ ⊢ Y → Γ ⊢ (X `∧ Y)
  inl : ∀ {X Y} → Γ ⊢ X → Γ ⊢ (X `∨ Y)
  inr : ∀ {X Y} → Γ ⊢ Y → Γ ⊢ (X `∨ Y)

Env : Nat → Set₁
Env n = Vec Set n

⟦_⟧ : ∀ {n} → P n → Env n → Set
⟦ `⊤     ⟧ Δ = ⊤
⟦ `⊥     ⟧ Δ = ⊥
⟦ X `∧ Y ⟧ Δ = ⟦ X ⟧ Δ × ⟦ Y ⟧ Δ
⟦ X `∨ Y ⟧ Δ = Either (⟦ X ⟧ Δ) (⟦ Y ⟧ Δ)
⟦ X `⇒ Y ⟧ Δ = (⟦ X ⟧ Δ) → (⟦ Y ⟧ Δ)
⟦ ?? n   ⟧ Δ = indexVec Δ n

⟦_⟧ctx : ∀ {n} → Ctx n → Env n → Set
⟦ Γ ⟧ctx Δ = All (λ A → ⟦ A ⟧ Δ) Γ


⊢-sound : ∀ {n} {Γ : Ctx n} {A : P n} → Γ ⊢ A → {Δ : Env n} → ⟦ Γ ⟧ctx Δ → ⟦ A ⟧ Δ
⊢-sound (var x)   γ   = lookup∈ γ x
⊢-sound tt        γ   = tt
⊢-sound (d₁ , d₂) γ   = (⊢-sound d₁ γ) , (⊢-sound d₂ γ)
⊢-sound (inl d)   γ   = left (⊢-sound d γ)
⊢-sound (inr d)   γ   = right (⊢-sound d γ)
⊢-sound (lam d)   γ z = ⊢-sound d (z ∷ γ)


QEnv : Nat → Set
QEnv n = Vec Type n

record ParsedType (n : Nat) : Set where
  constructor parsed
  field
    {#env} : Nat
    env    : QEnv #env
    lifter : P n → P #env
    type   : P #env
open ParsedType

liftP : {n : Nat} (k : Nat) → P n → P (k + n)
liftP k `⊤       = `⊤
liftP k `⊥       = `⊥
liftP k (A `∧ B) = liftP k A `∧ liftP k B
liftP k (A `∨ B) = liftP k A `∨ liftP k B
liftP k (A `⇒ B) = liftP k A `⇒ liftP k B
liftP k ( ?? x ) = ?? (raise k x)

{-# TERMINATING #-}
parseP : Type → TC (ParsedType 0)
parseP = loop []

  where
    strengthn : Arg Type → Type → Term → TC (Maybe Term)
    strengthn dom a t = do
      t' ← newMeta a
      (extendContext dom (unify t (weaken 1 t')) >> return (just t'))
        <|> (return nothing)

    fallback : {n : Nat} → QEnv n → Type → TC (ParsedType n)
    fallback Δ t = case findIndex Δ t of λ where
      nothing  → return (parsed (t ∷ Δ) (liftP 1) (?? 0))
      (just x) → return (parsed Δ id (?? x))

    loop : {n : Nat} → QEnv n → Type → TC (ParsedType n)
    loop Δ t = reduce t >>= λ where
      (def (quote ⊤) []) → return (parsed Δ id `⊤)
      (def (quote ⊥) []) → return (parsed Δ id `⊥)
      (def (quote Either) (_ ∷ _ ∷ (arg _ x) ∷ (arg _ y) ∷ [])) → do
        (parsed Δ₁ lift₁ X) ← loop Δ  x
        (parsed Δ₂ lift₂ Y) ← loop Δ₁ y
        return (parsed Δ₂ (lift₂ ∘ lift₁) (lift₂ X `∨ Y))
      (def (quote Σ) (_ ∷ _ ∷ ax@(arg _ x) ∷ (arg _ (lam _ (abs _ y))) ∷ [])) → do
        just y ← strengthn ax set! y
          where nothing → fallback Δ t
        (parsed Δ₁ lift₁ X) ← loop Δ  x
        (parsed Δ₂ lift₂ Y) ← loop Δ₁ y
        return (parsed Δ₂ (lift₂ ∘ lift₁) (lift₂ X `∧ Y))
      t@(pi ax@(arg _ x) (abs _ y)) → do
        just y ← strengthn ax set! y
          where nothing → fallback Δ t
        (parsed Δ₁ lift₁ X) ← loop Δ  x
        (parsed Δ₂ lift₂ Y) ← loop Δ₁ y
        return (parsed Δ₂ (lift₂ ∘ lift₁) (lift₂ X `⇒ Y))
      t → fallback Δ t

macro
  parse : Term → Term → TC ⊤
  parse t goal = do
    T ← parseP t
    result ← quoteTC T
    unify goal result

testType₁ : Set
testType₁ = ⊤ × ⊥ → Either ⊥ ⊤

testParse₁ : parse (testType₁) ≡ parsed [] _ ((`⊤ `∧ `⊥) `⇒ (`⊥ `∨ `⊤))
testParse₁ = refl

testType₂ : Set → Set
testType₂ A = A × ⊤ → Either ⊥ A

testParse₂ : ∀ {A} → parse (testType₂ A) ≡ parsed (var₀ 0 ∷ []) _ ((?? zero `∧ `⊤) `⇒ (`⊥ `∨ ?? zero))
testParse₂ = refl

assumption : ∀ {n} (Γ : Ctx n) (X : P n) → Maybe (X ∈ Γ)
assumption [] Y = nothing
assumption (X ∷ Γ)  Y with X == Y
assumption (X ∷ Γ) .X  | yes refl = just zero!
assumption (X ∷ Γ)  Y  | no x     = suc <$> assumption Γ Y

solveTauto : ∀ {n} (Γ : Ctx n) (X : P n) → Maybe (Γ ⊢ X)
solveTauto {n} Γ X = (var <$> assumption Γ X) <|> solveTautoAux X
  where
    solveTautoAux : (X : P n) → Maybe (Γ ⊢ X)
    solveTautoAux = λ where
      `⊤ → return tt
      `⊥ → nothing
      (X `∧ Y) → _,_ <$> solveTauto Γ X <*> solveTauto Γ Y
      (X `∨ Y) → (inl <$> solveTauto Γ X) <|> (inr <$> solveTauto Γ Y)
      (X `⇒ Y) → lam <$> solveTauto (X ∷ Γ) Y
      (?? x  ) → nothing

macro
  tauto : Term → TC ⊤
  tauto goal = do
    x ← inferType goal
    parsed Δ lift X ← parseP x
    case solveTauto [] X of λ where
      (just x) → do
        Δ ← traverse′ (unquoteTC {A = Set}) Δ
        let proof : ⟦ X ⟧ Δ
            proof = ⊢-sound x []
        unify goal =<< quoteTC proof
      nothing  → do
        X ← quoteTC X
        typeError (strErr "Failed to solve" ∷ termErr X ∷ [])


test₁ : ⊤
test₁ = tauto

test₂ : ⊥ → ⊥
test₂ = tauto

test₃ : ⊥ → ⊤ → ⊥ × ⊤
test₃ = tauto

test₄ : Either ⊥ ⊤
test₄ = tauto

test₅ : ⊤ → Either ⊤ ⊥
test₅ = tauto

module _ {A B C : Set} where

  test₇ : A → Either ⊥ A
  test₇ = tauto

  test₈ : A → B → A × B
  test₈ = tauto

  test₉ : A → (Either C (Either B A))
  test₉ = tauto
