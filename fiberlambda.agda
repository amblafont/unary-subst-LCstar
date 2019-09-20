{-# OPTIONS  --rewriting #-}
{-

(this file was tested with agda v2.6.0.1)

In this file, we consider the lambda calculus monad LC equipped
with a structure of reduction monads π₁,π₂: Red → LC × LC with (at least)
an action of the congruences rules for application and abstraction.

We construct π₁*,π₂*:Red* → LC × LC, the closure under composition and
identities of Red.  We show that Red* has an action of the congruence for unary
substitution: there exists a module morphism α : Red* × LC' → Red* such that
π₁* (α (m , t)) ≡ t { ⋆ := π₁* m}
π₂* (α (m , t)) ≡ t { ⋆ := π₂* m}

The construction of α and the proof that it has the desired properties is
very straigthforward once everything is settled (see the end of the file).

The main part of this file consists in building all the required structure.
We make heavy use of rewrite rules of agda, thus avoiding dealing too
much with non definitional equalities. Indeed, rewrite rules turn
propositional equalities into definitional ones.

In this file, we also show that Red* has an action of the transitivity rule.

Ambroise LAFONT 20/09/2019

-}

open import Level
open import Relation.Binary.PropositionalEquality public using (_≡_) renaming (refl to idp)
open import EqLib renaming (fst to ₁ ; snd to ₂ ; _∙_ to _◾_ )
open import Data.List public using (List; _∷_ ; map ; _++_) renaming ([] to nil)

-- option
data _+1 (X : Set) : Set where
   i : X → X +1
   ⋆ : X +1

-- some lemmas about map
map-∘ : ∀ {i j k} {A : Type i} {B : Type j} (f : A → B)
  {C : Type k} (g : C → A)  l → map f (map g l) ≡ map (λ x → f (g x)) l
map-∘ f g nil = idp
map-∘ f g (x ∷ l) = ap (f (g x) ∷_) (map-∘ f g l)

-- taken from Data.List.Properties
module _ {a b} {A : Set a} {B : Set b} where

  map-++-commute : ∀ (f : A → B) xs ys →
                   map f (xs ++ ys) ≡ map f xs ++ map f ys
  map-++-commute f nil       ys = idp
  map-++-commute f (x ∷ xs) ys = ap (f x ∷_) (map-++-commute f xs ys)


_+1f : ∀ {X Y : Set} (f : X → Y) → X +1 → Y +1
(f +1f) (i x) = i (f x)
(f +1f) ⋆ = ⋆

{- -- Lambda calculus

The syntax of the lambda calculus can be defined as the 
initial algebra of the endofunctor on [Set₀, Set] mapping a functor F
to X ↦ X + F(X +1) + F(X) × F(X), where Set₀ is the discretized category
of sets.

-}
data LC (X : Set ) : Set where
  η : X → LC X
  lam : LC  (X +1) → LC X
  app : LC X → LC X → LC X

-- LC': we define it separately in order to benefit from
-- the induction principle (which is not directly available if we define
-- LC' (X) directly  as LC (X +1))
data LC' (X : Set ) : Set where
  ⋆' : LC' X
  η' : X → LC' X
  lam' : LC'  (X +1) → LC' X
  app' : LC' X → LC' X → LC' X



-- renamings
_[_]r : ∀ {X Y : Set} (t : LC X) (f : X → Y) → LC Y
η x [ f ]r = η (f x)
lam t [ f ]r = lam (t [ f +1f ]r)
app t u [ f ]r = app (t [ f ]r)(u [ f ]r)

∂ : ∀ {X Y : Set}(f : X → LC Y) (t : X +1) → LC (Y +1)
∂ f (i x) = f x [ i ]r
∂ f ⋆ = η ⋆

-- definition of monadic substitution
_[_] : ∀ {X Y : Set} (t : LC X) (f : X → LC Y) → LC Y


η x [ f ] = f x
lam t [ f ] = lam (t [ ∂ f ])
app t u [ f ] = app (t [ f ])(u [ f ])

-- composition of renamings/substitutions
[]r[]r :
  ∀ {X : Set}(t : LC X){Y : Set}(f : X → Y){Z : Set}(g : Y →  Z) →
    ((t [ f ]r) [ g ]r) ≡ (t [ g ∘ f ]r)

[]r[]r (η x) f g = idp
[]r[]r (lam x) f g = ap lam ([]r[]r x (f +1f)(g +1f) ◾ ap (x [_]r) (λ= helper))
   where
     helper : (λ {a} → g +1f) ∘ (f +1f) ∼ (((λ {a} → g) ∘ f) +1f)
     helper (i x) = idp
     helper ⋆ = idp
[]r[]r (app t u) f g = ap2 app ([]r[]r t f g) ([]r[]r u f g)

[]r[] :
  ∀ {X : Set}(t : LC X){Y : Set}(f : X → Y){Z : Set}(g : Y → LC Z) →
    ((t [ f ]r) [ g ]) ≡ (t [ g ∘ f ])

[]r[] (η x) f g = idp
[]r[] (lam x) f g = ap lam ([]r[] x  (f +1f) ( ∂ g ) ◾ ap (x [_]) (λ= helper) )
  where
    helper : (λ {a} → ∂ g) ∘ (f +1f) ∼ ∂ ((λ {a} → g) ∘ f)
    helper (i x) = idp
    helper ⋆ = idp
[]r[] (app t u) f g = ap2 app ([]r[] t f g) ([]r[] u f g)

[][]r :
  ∀ {X : Set}(t : LC X){Y : Set}(f : X → LC Y){Z : Set}(g : Y → Z) →
    ((t [ f ]) [ g ]r) ≡ (t [ (λ x → (f x [ g ]r)) ])

[][]r (η x) f g = idp
[][]r (lam x) f g = ap lam ([][]r x (∂ f)(g +1f) ◾ ap (x [_]) (λ= helper) )
    where
       helper : (λ x₁ → ∂ f x₁ [ g +1f ]r) ∼ ∂ (λ x₁ → f x₁ [ g ]r)
       helper (i x) =  []r[]r (f x) i (g +1f) ◾ ! ([]r[]r (f x) g i)
       helper ⋆ = idp
[][]r (app t u) f g = ap2 app ([][]r t f g) ([][]r u f g)



[][] :
  ∀ {X : Set}(t : LC X){Y : Set}(f : X → LC Y){Z : Set}(g : Y → LC Z) →
    ((t [ f ]) [ g ]) ≡ (t [ ( λ x → (f x) [ g ] )  ])

[][] (η x) f g = idp
[][] {X}(lam x) {Y}f{Z} g = ap lam ([][] x (∂ f)(∂ g) ◾ ap (x [_]) (λ= helper))
  where
    helper : (x : X +1) → ( ∂ f x [ ∂ g ]) ≡ ∂ (λ x₁ → f x₁ [ g ]) x
    helper (i x) =   []r[] (f x) i (∂ g) ◾ ! ([][]r (f x) g i)
    -- helper (i x) =   []r[] (f x) i [ (λ x₁ → g x₁ [ i ]r) , η ⋆ ] ◾ ! ([][]r (f x) g i)

    helper ⋆ = idp
[][] (app t u) f g = ap2 app ([][] t f g) ([][] u f g)

-- a renaming is just a particular substitution
[]r=[] : ∀ {X Y : Set} t (f : X → Y) → t [ f ]r ≡ t [ (η ∘ f) ]
[]r=[] (η x) f = idp
[]r=[] (lam x) f = ap lam ([]r=[] x (f +1f) ◾ ap (x [_]) (λ= helper))
  where
    helper :  (λ {a} → η) ∘ (f +1f) ∼ ∂ ((λ {a} → η) ∘ f)
    helper (i x) = idp
    helper ⋆ = idp
[]r=[] (app t u) f = ap2 app ([]r=[] t f) ([]r=[] u f)

{-# REWRITE []r=[] #-}
{-# REWRITE [][] #-}

{- -----

Interaction between LC and LC'

----   -}

ι : ∀ {X : Set} (t : LC X) → LC' X
ι (η x) = η' x
ι (lam x) = lam' (ι x)
ι (app t u) = app' (ι t)(ι u)

-- module structure on LC' (just the substitution)
_[_]' : ∀ {X Y : Set} (t : LC' X) (f : X → LC Y) → LC' Y
⋆' [ f ]' = ⋆'
η' x [ f ]' = ι (f x)
lam' x [ f ]' = lam' (x [ ∂ f ]')
app' t u [ f ]' = app' (t [ f ]')(u [ f ]')


-- This is the unary substitution
_[_]₁' : ∀ {X : Set}(t : LC' X)(z : LC X) → LC X
⋆' [ z ]₁' = z
η' x [ z ]₁' = η x
lam' x [ z ]₁' = lam (x [ z [ i ]r ]₁')
app' t u [ z ]₁' = app (t [ z ]₁')(u [ z ]₁')


{-
We postulate the existence of a reduction module over LC.
Postulating it has the technical advantage that Agda accept rewrite rules.

We don't postulate the fact that the identity substitution is neutral, as
it is not needed for the purpose of our proof.
-}
postulate
  Red : Set → Set
  _[_]R : ∀ {X Y}(m : Red X)(f : X → LC Y) → Red Y

  [][]R :
    ∀ {X : Set}(m : Red X){Y : Set}(f : X → LC Y){Z : Set}(g : Y → LC Z) →
    ((m [ f ]R) [ g ]R) ≡ ( m [ ( λ x → (f x) [ g ] )  ]R )

  -- π₁ is called source in the paper
  -- π₂ is called target in the paper
  π₁ : ∀ {X} → Red X → LC X
  π₂ : ∀ {X} → Red X → LC X
  π₁[] : ∀ {X Y}(m : Red X)(f : X → LC Y) → π₁ (m [ f ]R) ≡ π₁ m [ f ]
  π₂[] : ∀ {X Y}(m : Red X)(f : X → LC Y) → π₂ (m [ f ]R) ≡ π₂ m [ f ]

  -- Actions for the congruence rules of abstraction and application
  cong-abs : ∀ {X} → Red (X +1) → Red X
  cong-appl : ∀ {X} → LC X → Red X → Red X
  cong-appr : ∀ {X} → LC X → Red X → Red X

  π₁abs : ∀{X}(m : Red (X +1))→ π₁ (cong-abs m) ≡ lam (π₁ m)
  π₂abs : ∀{X}(m : Red (X +1))→ π₂ (cong-abs m) ≡ lam (π₂ m)

  π₁appl : ∀{X}(t : LC X)(m : Red X)→ π₁ (cong-appl t m) ≡ app (π₁ m) t
  π₂appl : ∀{X}(t : LC X)(m : Red X)→ π₂ (cong-appl t m) ≡ app (π₂ m) t

  π₁appr : ∀{X}(t : LC X)(m : Red X)→ π₁ (cong-appr t m) ≡ app t (π₁ m)
  π₂appr : ∀{X}(t : LC X)(m : Red X)→ π₂ (cong-appr t m) ≡ app t (π₂ m)

  abs[] : ∀ {X Y : Set}(f : X → LC Y) (m : Red (X +1)) →
     (cong-abs m) [ f ]R ≡ cong-abs (m [ ∂ f  ]R)
  appl[] : ∀ {X Y : Set}(f : X → LC Y) (t : LC X)(m : Red (X )) →
     (cong-appl t m) [ f ]R ≡ cong-appl (t [ f ]) (m [ f  ]R)
  appr[] : ∀ {X Y : Set}(f : X → LC Y) (t : LC X)(m : Red (X )) →
     (cong-appr t m) [ f ]R ≡ cong-appr (t [ f ]) (m [ f  ]R)

-- all these equalities become definitional
{-# REWRITE [][]R #-}
{-# REWRITE π₁[] #-}
{-# REWRITE π₂[] #-}
{-# REWRITE π₁abs #-}
{-# REWRITE π₂abs #-}
{-# REWRITE π₁appl #-}
{-# REWRITE π₂appl #-}
{-# REWRITE π₁appr #-}
{-# REWRITE π₂appr #-}
{-# REWRITE abs[] #-}
{-# REWRITE appl[] #-}
{-# REWRITE appr[] #-}


{-

Now we build Red*, the closure under identity and composition of Red


-}

-- [wRed+ m0 (m1 ; m2 ; m3 ; ..)] states that m0 ; m1 ; m2 ; m3 is a valid
-- sequence of reductions: that is, the source of m_i is the target of m_i+1.
wRed+ : ∀ {X : Set} → Red X → List (Red X) → Set
wRed+ h nil = ⊤
wRed+ h (x ∷ m) = (π₁ h ≡ π₂ x) × wRed+ x m

-- This defines the closure under identity and composition:
data Red* : Set → Set where
  -- it is either a reflexivity
  refl : ∀ {X : Set} → LC X → Red* X
  -- or a non empty list, that is, a list [l] of reductions and a reduction [h]
  -- such that h ; l is a valid sequence of reductions
  _﹐_∣_ : ∀ {X : Set} →  (l : List (Red X))→ (h : Red X) → wRed+ h l  → Red* X

{- ----


We show that Red* has a module structure


---- -}

_[_]w+ : ∀ {X Y}{h : Red X}{l}(w : wRed+ h l)(f : X → LC Y) → wRed+ (h [ f ]R) (map (_[ f ]R) l)
_[_]w+ {l = nil} w f = w
_[_]w+ {l = x ∷ l} (eq , w) f = ap (_[ f ]) eq , (w [ f ]w+)

_[_]* : ∀ {X Y}(m : Red* X)(f : X → LC Y) → Red* Y
refl x [ f ]* = refl (x [ f ])
(l ﹐ h ∣ x) [ f ]* = map (_[ f ]R) l ﹐ h [ f ]R ∣ (x [ f ]w+)

[][]+₁ : ∀ {X Y Z : Set}(f : X → LC Y)(g : Y → LC Z) l →
  map (_[ g ]R) (map (_[ f ]R) l) ≡ map (_[ (λ x₁ → f x₁ [ g ]) ]R) l

[][]+₁ f g l =  map-∘ (_[ g ]R) (_[ f ]R) l

{-# REWRITE [][]+₁ #-}

[][]w+ : ∀ {X Y Z : Set}(f : X → LC Y)(g : Y → LC Z)
  {h}{l}(x : wRed+ h l) →
  ((x [ f ]w+) [ g ]w+) ≡ (x [ (λ x₁ → f x₁ [ g ]) ]w+)

[][]w+ f g {l = nil} w = idp
[][]w+ f g {l = x ∷ l} w = ap2 _,_ (∘-ap _[ g ] _[ f ] (₁ w)) ([][]w+ f g  (₂ w))

[][]* :
  ∀ {X : Set}(m : Red* X){Y : Set}(f : X → LC Y){Z : Set}(g : Y → LC Z) →
    ((m [ f ]*) [ g ]*) ≡ ( m [ ( λ x → (f x) [ g ] )  ]* )

[][]* (refl x) f g = idp
[][]* (l ﹐ h ∣ x) f g = ap (_ ﹐ _ ∣_) ([][]w+ f g x)

{-# REWRITE [][]* #-}


{-

Next, we construct  πᵢ* : Red* → LC and show that they are module morphisms
(they commute with substitution).

-}

π₁+ : {X : Set} → (t : Red X) → (l : List (Red X)) → LC X
π₁+ t nil = π₁ t
π₁+ t (x ∷ l) = π₁+ x l

π₂* : {X : Set} → Red* X → LC X
π₂* (refl x) =  x
π₂* (l ﹐ h ∣ _) = π₂ h

π₁* : {X : Set} → Red* X → LC X
π₁* (refl x) =  x
π₁* (l ﹐ h ∣ _) = π₁+ h l

π₁+[] : ∀ {X Y : Set}(h : Red X)(l : List (Red X))(f : X → LC Y) → π₁+ (h [ f ]R) (map (_[ f ]R) l) ≡ (π₁+ h l [ f ])

π₁+[] h nil f = idp
π₁+[] h (x ∷ l) f = π₁+[] x l f

{-# REWRITE π₁+[] #-}

π₁*[] : ∀ {X Y}(m : Red* X)(f : X → LC Y) → π₁* ( m [ f ]*) ≡ ((π₁* m) [ f ])
π₁*[] (refl x) f = idp
π₁*[] (l ﹐ h ∣ x) f = idp

{-# REWRITE π₁*[] #-}

π₂*[] : ∀ {X Y}(m : Red* X)(f : X → LC Y) → π₂* ( m [ f ]*) ≡ ((π₂* m) [ f ])
π₂*[] (refl x) f = idp
π₂*[] (l ﹐ h ∣ x) f = idp

{-# REWRITE π₂*[] #-}

{- -------------

We give Red* actions of the congruence rules application and abstraction

- ----------------- -}

wcong-abs+ : ∀ {X : Set}{h : Red (X +1)}{l} (w : wRed+ h l) → wRed+ (cong-abs h)(map cong-abs l)
wcong-abs+ {h = h} {nil} w = w
wcong-abs+ {h = h} {x ∷ l} (eq , w) = ap lam eq , wcong-abs+ w


wcong-appl+ : ∀ {X : Set}(t : LC X){h : Red X}{l} (w : wRed+ h l)
   → wRed+ (cong-appl t h)(map (cong-appl t) l)
wcong-appl+ t {l = nil} w = w
wcong-appl+ t {l = x ∷ l} (eq , w) = (ap (λ t → app t _) eq) , wcong-appl+ t w

wcong-appr+ : ∀ {X : Set}(t : LC X){h : Red X}{l} (w : wRed+ h l)
   → wRed+ (cong-appr t h)(map (cong-appr t) l)
wcong-appr+ t {l = nil} w = w
wcong-appr+ t {l = x ∷ l} (eq , w) = (ap (λ t → app _ t) eq) , wcong-appr+ t w

-- congruence for abstraction
cong-abs* : ∀ {X} → Red* (X +1) → Red* X
cong-abs* (refl x) = refl (lam x)
cong-abs* (l ﹐ h  ∣ x) =  map cong-abs l ﹐ cong-abs h ∣ wcong-abs+ x

-- left congruence for application
cong-appl* : ∀ {X} → LC X → Red* X → Red* X
cong-appl* t (refl x) = refl (app x t)
cong-appl* t (l ﹐ h ∣ x) = map (cong-appl t) l ﹐ cong-appl t h ∣ wcong-appl+ t x

-- right congruence for application
cong-appr* : ∀ {X} → LC X → Red* X → Red* X
cong-appr* t (refl x) = refl (app t x)
cong-appr* t (l ﹐ h ∣ x) = map (cong-appr t) l ﹐ cong-appr t h ∣ wcong-appr+ t x

{-
The next block shows that these are reductions between the expected terms
-}
π₁+abs : ∀ {X}(t : Red (X +1))  l →  π₁+ (cong-abs t) (map (cong-abs ) l) ≡ lam (π₁+ t l)
π₁+abs t nil = idp
π₁+abs t (x ∷ l) = π₁+abs x l

{-# REWRITE π₁+abs #-}

π₁*abs : ∀{X}(m : Red* (X +1))→ π₁* (cong-abs* m) ≡ lam (π₁* m)
π₁*abs (refl x) = idp
π₁*abs (l ﹐ h ∣ x) = idp

{-# REWRITE π₁*abs #-}

π₂*abs : ∀{X}(m : Red* (X +1))→ π₂* (cong-abs* m) ≡ lam (π₂* m)
π₂*abs (refl x) = idp
π₂*abs (l ﹐ h ∣ x) = idp

{-# REWRITE π₂*abs #-}

π₁+appr : ∀ {X}(t : LC X) h l → π₁+ (cong-appr t h) (map (cong-appr t) l) ≡ app t (π₁+ h l)
π₁+appr t h nil = idp
π₁+appr t h (x ∷ l) = π₁+appr t x l

{-# REWRITE π₁+appr #-}

π₁*appr : ∀{X}(t : LC X)(m : Red* X)→ π₁* (cong-appr* t m) ≡ app t (π₁* m)
π₁*appr t (refl x) = idp
π₁*appr t (l ﹐ h ∣ x) = idp

{-# REWRITE π₁*appr #-}

π₂*appr : ∀{X}(t : LC X)(m : Red* X)→ π₂* (cong-appr* t m) ≡ app t (π₂* m)
π₂*appr t (refl x) = idp
π₂*appr t (l ﹐ h ∣ x) = idp

{-# REWRITE π₂*appr #-}

π₁+appl : ∀ {X}(t : LC X) h l → π₁+ (cong-appl t h) (map (cong-appl t) l) ≡ app (π₁+ h l) t
π₁+appl t h nil = idp
π₁+appl t h (x ∷ l) = π₁+appl t x l

{-# REWRITE π₁+appl #-}

π₁*appl : ∀{X}(t : LC X)(m : Red* X)→ π₁* (cong-appl* t m) ≡ app (π₁* m) t
π₁*appl t (refl x) = idp
π₁*appl t (l ﹐ h ∣ x) = idp

{-# REWRITE π₁*appl #-}

π₂*appl : ∀{X}(t : LC X)(m : Red* X)→ π₂* (cong-appl* t m) ≡ app (π₂* m) t
π₂*appl t (refl x) = idp
π₂*appl t (l ﹐ h ∣ x) = idp

{-# REWRITE π₂*appl #-}

{-

The next block show that these commute with substitution.
This terminates the proof that Red* has an action for congruence
of application and abstraction

-}

cong-abs+[]₁ : ∀ {X Y : Set}(f : X → LC Y) {h : Red (X +1)} l  →
   (map (_[ f ]R) (map cong-abs l)) ≡ map cong-abs (map (_[ ∂ f ]R) l)

cong-abs+[]₁ f l = map-∘ (_[ f ]R) cong-abs l ◾ ! (map-∘ cong-abs (_[ ∂ f ]R) l)

{-# REWRITE cong-abs+[]₁ #-}



cong-abs+[]w : ∀ {X Y : Set}(f : X → LC Y) {h : Red (X +1)} {l} (x : wRed+ h l) →
  (wcong-abs+ x [ f ]w+) ≡  wcong-abs+ (x [ ∂ f ]w+)
cong-abs+[]w f {l = nil} w = idp
cong-abs+[]w f {l = x ∷ l} w = ap2 _,_ (∘-ap (_[ f ]) lam (₁ w) ◾ ap-∘ lam _[ ∂ f ] (₁ w)) (cong-abs+[]w f {l = l} (₂ w))


cong-abs*[] : ∀ {X Y : Set}(f : X → LC Y) (m : Red* (X +1)) → (cong-abs* m) [ f ]* ≡ cong-abs* (m [ ∂ f  ]*)
cong-abs*[] f (refl x) = idp
cong-abs*[] f (l ﹐ h ∣ x) = ap (_ ﹐ _ ∣_) (cong-abs+[]w f x)

{-# REWRITE cong-abs*[] #-}

cong-appl+[]₁ : ∀ {X Y : Set}(f : X → LC Y)
   (t  : LC X)(m : Red* (X ))l →
  map (_[ f ]R) (map (cong-appl t) l) ≡
  map (cong-appl (t [ f ])) (map (_[ f ]R) l)

cong-appl+[]₁ f t m l = map-∘ (_[ f ]R) (cong-appl t) l ◾ ! ( map-∘ (cong-appl (t [ f ])) (_[ f ]R) l )

{-# REWRITE cong-appl+[]₁ #-}

cong-appl+[]w : ∀ {X Y : Set}(f : X → LC Y) (t  : LC X)
  {h : Red (X )} {l} (x : wRed+ h l)
  →
  (wcong-appl+ t x [ f ]w+) ≡ wcong-appl+ (t [ f ]) (x [ f ]w+)

cong-appl+[]w f t {l = nil} x = idp
cong-appl+[]w f t {l = x₁ ∷ l} x =
   ap2 _,_
   (∘-ap (_[ f ]) (λ z → app z t) (₁ x) ◾ ap-∘ (λ z → app z (t [ f ])) _[ f ] (₁ x))
   (cong-appl+[]w f t (₂ x))

cong-appl*[] : ∀ {X Y : Set}(f : X → LC Y) (t  : LC X)(m : Red* (X )) → (cong-appl* t m) [ f ]* ≡ cong-appl* (t [ f ])(m [ f  ]*)
cong-appl*[] f t (refl x) = idp
cong-appl*[] f t (l ﹐ h ∣ x) =  ap (_ ﹐ _ ∣_) (cong-appl+[]w f t x)

{-# REWRITE cong-appl*[] #-}

cong-appr+[]₁ : ∀ {X Y : Set}(f : X → LC Y)
   (t  : LC X)(m : Red* (X ))l →
  map (_[ f ]R) (map (cong-appr t) l) ≡
  map (cong-appr (t [ f ])) (map (_[ f ]R) l)

cong-appr+[]₁ f t m l = map-∘ (_[ f ]R) (cong-appr t) l ◾ ! ( map-∘ (cong-appr (t [ f ])) (_[ f ]R) l )

{-# REWRITE cong-appr+[]₁ #-}

cong-appr+[]w : ∀ {X Y : Set}(f : X → LC Y) (t  : LC X)
  {h : Red (X )} {l} (x : wRed+ h l)
  →
  (wcong-appr+ t x [ f ]w+) ≡ wcong-appr+ (t [ f ]) (x [ f ]w+)

cong-appr+[]w f t {l = nil} x = idp
cong-appr+[]w f t {l = x₁ ∷ l} x =
   ap2 _,_
   (∘-ap (_[ f ]) (λ z → app t z) (₁ x) ◾ ap-∘ (λ z → app (t [ f ]) z) _[ f ] (₁ x))
   (cong-appr+[]w f t (₂ x))

cong-appr*[] : ∀ {X Y : Set}(f : X → LC Y) (t  : LC X)(m : Red* (X )) → (cong-appr* t m) [ f ]* ≡ cong-appr* (t [ f ])(m [ f  ]*)
cong-appr*[] f t (refl x) = idp
cong-appr*[] f t (l ﹐ h ∣ x) =  ap (_ ﹐ _ ∣_) (cong-appr+[]w f t x)

{-# REWRITE cong-appr*[] #-}


{-

Next, we show that Red* has an action of the transitivity rule

-}

w^^+ : ∀ {X : Set} {h : Red X} {l} (w : wRed+ h l){h'} {l'} (w' : wRed+ h' l')
   (eq : π₁+ h l ≡ π₂ h') → wRed+ h (l ++ h' ∷ l')
w^^+ {l = nil} w {l' = l'} w' eq = eq ,  w'
w^^+ {l = x ∷ l} (eq , w) {l' = l'} w' eq' = eq , (w^^+ w w' eq')

-- the transitivity rule
_^^_∣_ : {X : Set} (m : Red* X)(n : Red* X)(eq : π₁* n ≡ π₂* m) → Red* X
m ^^ refl x ∣ eq = m
refl x₁ ^^ l ﹐ h ∣ x ∣ eq = l ﹐ h ∣ x
(l' ﹐ h' ∣ x') ^^ l ﹐ h ∣ x ∣ eq = (l ++ (h' ∷ l')) ﹐ h ∣ w^^+ x x' eq

{-

The next block shows that the transitivty reduction happens between
the expected terms

-}
π₁++ : ∀ {X : Set} (h : Red X)l h' l' → π₁+ h (l ++ h' ∷ l') ≡ π₁+ h' l'
π₁++ h nil h' l' = idp
π₁++ h (x ∷ l) h' l' = π₁++ x l h' l'

{-# REWRITE π₁++ #-}

π₁^^ : {X : Set} (m : Red* X)(n : Red* X)(eq : π₁* n ≡ π₂* m)
   → π₁* (m ^^ n ∣ eq) ≡ π₁* m
π₁^^ m (refl x) eq = idp
π₁^^ (refl x₁) (l ﹐ h ∣ x) eq = eq
π₁^^ (l' ﹐ h' ∣ w') (l ﹐ h ∣ x) eq = idp

π₂^^ : {X : Set} (m : Red* X)(n : Red* X)(eq : π₁* n ≡ π₂* m)
   → π₂* (m ^^ n ∣ eq) ≡ π₂* n
π₂^^ m (refl x) eq = ! eq
π₂^^ (refl x₁) (l ﹐ h ∣ x) eq = idp
π₂^^ (l₁ ﹐ h₁ ∣ x₁) (l ﹐ h ∣ x) eq = idp

{-# REWRITE π₁^^ #-}
{-# REWRITE π₂^^ #-}
{-

The next block shows that the transitivity reduction commutes with substitution.
This terminates the proof that Red* has an action of the transitivity reduction
rule.

-}

^^+[] : ∀ {X Y : Set}(f : X → LC Y)l l' h' →
   map (_[ f ]R) (l ++ h' ∷ l') ≡ (map (_[ f ]R) l ++ (h' [ f ]R) ∷ map (_[ f ]R) l')

^^+[] f l l' h' = map-++-commute (_[ f ]R) l (h' ∷ l')
{-# REWRITE ^^+[] #-}

^^+[]w : ∀ {X Y : Set}(f : X → LC Y) -- (m : Red* X)(n : Red* X)
  {h}{l}{h'}{l'}
  (x : wRed+ {X = X} h l)(x' : wRed+ {X = X} h' l')
  (eq : π₁+ h l ≡ π₂ h')
  →
  (w^^+ x x' eq [ f ]w+) ≡ w^^+ (x [ f ]w+) (x' [ f ]w+) (ap (_[ f ]) eq)

^^+[]w f {l = nil} {l' = l'} x x' eq = idp
^^+[]w f {l = x₁ ∷ l} {l' = l'} x x' eq = ap (_ ,_) (^^+[]w f (₂ x) x' eq)


^^[] : ∀ {X Y : Set}(f : X → LC Y) (m : Red* X)(n : Red* X)(eq : π₁* n ≡ π₂* m) →
  (m ^^ n ∣ eq) [ f ]* ≡ ((m [ f ]*) ^^ (n [ f ]*) ∣ ap (_[ f ]) eq)

^^[] f m (refl x) eq = idp
^^[] f (refl x₁) (l ﹐ h ∣ x) eq = idp
^^[] f (l' ﹐ h' ∣ x') (l ﹐ h ∣ x) eq = ap (_ ﹐ _ ∣_) (^^+[]w f x x' eq)

{-# REWRITE ^^[] #-}






{- ----------------------


Proposition 8.3 of the paper :
construction of α : LC' × Red(LC*) → Red(LC*)


------------------------ -}

-- binary congruence for application (obtained by composing by transitivity
-- the left and right congruence for application)
cong-app* : ∀ {X} → Red* X → Red* X → Red* X
cong-app* m n = cong-appl* (π₁* n) m ^^ cong-appr* (π₂* m) n ∣ idp

-- First step of the proof: build the collection of functions
α : {X : Set}(T : (LC' ) X ) (m : Red* X) → Red* X
α ⋆' m = m
α (η' x) m = refl (η x)
α (lam' T) m = cong-abs* (α T (m [ η ∘ i ]*))
α (app' T U) m = cong-app* (α T m) (α U m)


-- Second step:
--   i)  α ∘ ι = refl
αι : {X : Set}(T : (LC ) X ) (m : Red* X) → α (ι T) m ≡ refl T
αι (η x) m = idp
αι (lam x) m rewrite αι x (m [ η ∘ i ]*) = idp
αι (app T U) m rewrite αι T m | αι U m = idp


--  ii) α is a module morphism, i.e. commutes with substitution
α[] : ∀ {X Y : Set}(f : X → LC Y)(T : LC' X)(m  : Red* X) →
  ( ((α T m) [ f ]*) ) ≡  (α (T [ f ]') (m [ f ]*))

α[] f ⋆' m = idp
α[] f (η' x) m = ! ( αι (f x) (m [ f ]*) )
α[] f (lam' x) m rewrite (α[] (∂ f) x (m [ η ∘ i ]*)) = idp
α[] f (app' T U) m  =  ap2 cong-app* (α[] f T m) (α[] f U m)

-- Third step: the reduction lies between the expected terms
π₁α : {X : Set} (T : LC' X)(m : Red* X) → π₁* (α T m) ≡ (T [ π₁* m ]₁')
π₁α ⋆' m = idp
π₁α (η' x) m = idp
π₁α (lam' x) m rewrite π₁α x (m [ (λ x₁ → η (i x₁)) ]*) = idp
π₁α (app' T U) m rewrite π₁α T m | π₁α U m = idp

π₂α : {X : Set} (T : LC' X)(m : Red* X) → π₂* (α T m) ≡ (T [ π₂* m ]₁')
π₂α ⋆' m = idp
π₂α (η' x) m = idp
π₂α (lam' x) m rewrite π₂α x (m [ (λ x₂ → η (i x₂)) ]*) = idp
π₂α (app' T U) m rewrite π₂α T m | π₂α U m = idp
