
open import Prelude
open import Container.List
open import Tactic.Reflection
open import Tactic.Deriving.Eq

data P : Set where
  `⊤   : P
  `⊥   : P
  _`∧_ : P → P → P
  _`∨_ : P → P → P
  _`⇒_ : P → P → P

unquoteDecl eqP = deriveEq eqP (quote P)

Ctx = List P

data _⊢_ (Γ : Ctx) : P → Set where
  var : ∀ {X} → X ∈ Γ → Γ ⊢ X
  lam : ∀ {X Y} → (X ∷ Γ) ⊢ Y → Γ ⊢ (X `⇒ Y)
  tt  : Γ ⊢ `⊤
  _,_ : ∀ {X Y} → Γ ⊢ X → Γ ⊢ Y → Γ ⊢ (X `∧ Y)
  inl : ∀ {X Y} → Γ ⊢ X → Γ ⊢ (X `∨ Y)
  inr : ∀ {X Y} → Γ ⊢ Y → Γ ⊢ (X `∨ Y)

⟦_⟧ : P → Set
⟦ `⊤     ⟧ = ⊤
⟦ `⊥     ⟧ = ⊥
⟦ X `∧ Y ⟧ = ⟦ X ⟧ × ⟦ Y ⟧
⟦ X `∨ Y ⟧ = Either ⟦ X ⟧ ⟦ Y ⟧
⟦ X `⇒ Y ⟧ = ⟦ X ⟧ → ⟦ Y ⟧

⟦_⟧ctx : Ctx → Set
⟦_⟧ctx = All ⟦_⟧

⊢-sound : ∀ {Γ P} → Γ ⊢ P → ⟦ Γ ⟧ctx → ⟦ P ⟧
⊢-sound (var x)   γ   = lookup∈ γ x
⊢-sound tt        γ   = tt
⊢-sound (d₁ , d₂) γ   = (⊢-sound d₁ γ) , (⊢-sound d₂ γ)
⊢-sound (inl d)   γ   = left (⊢-sound d γ)
⊢-sound (inr d)   γ   = right (⊢-sound d γ)
⊢-sound (lam d)   γ z = ⊢-sound d (z ∷ γ)


strengthn : Arg Type → Type → Term → TC Term
strengthn dom a t = do
  t' ← newMeta a
  extendContext dom (unify t (weaken 1 t'))
  return t'

{-# TERMINATING #-}
parseP : Term → TC P
parseP t = reduce t >>= λ where
    (def (quote ⊤) []) → return `⊤
    (def (quote ⊥) []) → return `⊥
    (def (quote Either) (_ ∷ _ ∷ (arg _ x) ∷ (arg _ y) ∷ [])) → do
      X ← parseP x
      Y ← parseP y
      return (X `∨ Y)
    (def (quote Σ) (_ ∷ _ ∷ ax@(arg _ x) ∷ (arg _ (lam _ (abs _ y))) ∷ [])) → do
      X ← parseP x
      y ← strengthn ax set! y <|> errorNotAProp t
      Y ← parseP y
      return (X `∧ Y)
    t@(pi ax@(arg _ x) (abs _ y)) → do
      X ← parseP x
      y ← strengthn ax set! y <|> errorNotAProp t
      Y ← parseP y
      return (X `⇒ Y)
    t → errorNotAProp t

  where
    errorNotAProp : ∀ {A} → Term → TC A
    errorNotAProp t = typeError (strErr "Parsing failed: " ∷ termErr t ∷ strErr "is not a proposition!" ∷ [])

macro
  parse : Term → Term → TC ⊤
  parse t goal = do
    T ← parseP t
    result ← quoteTC T
    unify goal result

testType₁ : Set
testType₁ = ⊤ × ⊥ → Either ⊥ ⊤

testParse₁ : parse (testType₁) ≡ ((`⊤ `∧ `⊥) `⇒ (`⊥ `∨ `⊤))
testParse₁ = refl

assumption : (Γ : Ctx) (X : P) → Maybe (X ∈ Γ)
assumption [] Y = nothing
assumption (X ∷ Γ)  Y with X == Y
assumption (X ∷ Γ) .X  | yes refl = just zero!
assumption (X ∷ Γ)  Y  | no x     = suc <$> assumption Γ Y

solveTauto : (Γ : List P) (X : P) → Maybe (Γ ⊢ X)
solveTauto Γ X = (var <$> assumption Γ X) <|> solveTautoAux X
  where
    solveTautoAux : (X : P) → Maybe (Γ ⊢ X)
    solveTautoAux = λ where
      `⊤ → return tt
      `⊥ → nothing
      (X `∧ Y) → do
        x ← solveTauto Γ X
        y ← solveTauto Γ Y
        return (x , y)
      (X `∨ Y) → (inl <$> solveTauto Γ X) <|> (inr <$> solveTauto Γ Y)
      (X `⇒ Y) → lam <$> solveTauto (X ∷ Γ) Y

macro
  tauto : Term → TC ⊤
  tauto goal = do
    X ← parseP =<< inferType goal
    case solveTauto [] X of λ where
      (just x) → let proof : ⟦ X ⟧
                     proof = ⊢-sound x []
                 in unify goal =<< quoteTC proof
      nothing  → typeError (strErr "Failed to solve" ∷ [])

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
