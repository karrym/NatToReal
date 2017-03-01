module Int where

open import Data.Product
open import Data.Sum as S
open import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Core
open import Relation.Binary
open import Function.Equality hiding (cong)
open import Data.Empty
import Level
open import Nat

open Eq.≡-Reasoning

ℤb : Set
ℤb = ℕ × ℕ

_≡ℤ_ : ℤb → ℤb → Set
(a , b) ≡ℤ (c , d) = a + d ≡ b + c

reflexive : {x : ℤb} → x ≡ℤ x
reflexive {a , b} = +-comm a b
symmetric : (x y : ℤb) → x ≡ℤ y → y ≡ℤ x
symmetric (a , b) (c , d) a+d≡b+c = begin
        c + b
    ≡⟨ +-comm c b ⟩
        b + c
    ≡⟨ sym a+d≡b+c ⟩
        a + d
    ≡⟨ +-comm a d ⟩
        d + a
    ∎
transitive : ∀ {x y z : ℤb} → x ≡ℤ y → y ≡ℤ z → x ≡ℤ z
transitive {a , b} {c , d} {e , f} a+d≡b+c c+f≡d+e = lem (begin
        a + ((d + c) + f)
    ≡⟨ cong (λ x → a + x) (sym (+-assoc d c f)) ⟩
        a + (d + (c + f))
    ≡⟨ +-assoc a d (c + f) ⟩
        (a + d) + (c + f)
    ≡⟨ cong (λ x → x + (c + f)) a+d≡b+c ⟩
        (b + c) + (c + f)
    ≡⟨ cong (λ x → (b + c) + x) c+f≡d+e ⟩
        (b + c) + (d + e)
    ≡⟨ sym (+-assoc b c (d + e)) ⟩
        b + (c + (d + e))
    ≡⟨ cong (λ x → b + x) (+-assoc c d e) ⟩
        b + ((c + d) + e)
    ∎)
    where
    lem : (a + ((d + c) + f)) ≡ (b + ((c + d) + e)) → (a + f) ≡ (b + e)
    lem p = +-rCancel (a + f) (b + e) (d + c) (begin
            (a + f) + (d + c)
        ≡⟨ sym (+-assoc a f (d + c)) ⟩
            a + (f + (d + c))
        ≡⟨ cong (λ x → a + x) (+-comm f (d + c)) ⟩
            a + ((d + c) + f)
        ≡⟨ p ⟩
            b + ((c + d) + e)
        ≡⟨ cong (λ x → b + x) (cong (λ x → x + e) (+-comm c d)) ⟩
            b + ((d + c) + e)
        ≡⟨ cong (λ x → b + x) (+-comm (d + c) e) ⟩
            b + (e + (d + c))
        ≡⟨ +-assoc b e (d + c) ⟩
            (b + e) + (d + c)
        ∎)

≡ℤ-eq : IsEquivalence _≡ℤ_
≡ℤ-eq = record
        { refl = λ {x} → reflexive {x}
        ; sym = λ {x y} → symmetric x y
        ; trans = λ {x y z} → transitive {x} {y} {z} }

ℤ : Setoid (Level.zero) (Level.zero)
ℤ = record { Carrier = ℤb ; _≈_ = _≡ℤ_ ; isEquivalence = ≡ℤ-eq }

≡ℤ-≡ : {a b : ℤb} → a ≡ b → a ≡ℤ b
≡ℤ-≡ {x , y} {.(x , y)} refl = +-comm x y

import Relation.Binary.EqReasoning as EqR
open EqR ℤ renaming
    ( begin_ to beginℤ_
    ; _≡⟨_⟩_ to _≡ℤ⟨_⟩_
    ; _∎ to _ℤ∎
    )

_+ℤ_ : ℤb → ℤb → ℤb
(a , b) +ℤ (c , d) = (a + c , b + d)

_*ℤ_ : ℤb → ℤb → ℤb
(a , b) *ℤ (c , d) = ((a * c) + (b * d) , (a * d) + (b * c))

+ℤ-lUniv : (a b c : ℤb) → a ≡ℤ b → (a +ℤ c) ≡ℤ (b +ℤ c)
+ℤ-lUniv (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) a₁+b₂≡a₂+b₁ = lem
    where
        lem : (a₁ + c₁) + (b₂ + c₂) ≡ (a₂ + c₂) + (b₁ + c₁)
        lem = begin
                (a₁ + c₁) + (b₂ + c₂)
            ≡⟨ sym (+-assoc a₁ c₁ (b₂ + c₂)) ⟩
                a₁ + (c₁ + (b₂ + c₂))
            ≡⟨ cong (λ x → a₁ + x) (+-assoc c₁ b₂ c₂) ⟩
                a₁ + ((c₁ + b₂) + c₂)
            ≡⟨ cong (λ x → a₁ + x) (cong (λ x → x + c₂) (+-comm c₁ b₂)) ⟩
                a₁ + ((b₂ + c₁) + c₂)
            ≡⟨ cong (λ x → a₁ + x) (sym (+-assoc b₂ c₁ c₂)) ⟩
                a₁ + (b₂ + (c₁ + c₂))
            ≡⟨ +-assoc a₁ b₂ (c₁ + c₂) ⟩
                (a₁ + b₂) + (c₁ + c₂)
            ≡⟨ cong (λ x → x + (c₁ + c₂)) a₁+b₂≡a₂+b₁ ⟩
                (a₂ + b₁) + (c₁ + c₂)
            ≡⟨ sym (+-assoc a₂ b₁ (c₁ + c₂)) ⟩
                a₂ + (b₁ + (c₁ + c₂))
            ≡⟨ cong (λ x → a₂ + x) (+-assoc b₁ c₁ c₂) ⟩
                a₂ + ((b₁ + c₁) + c₂)
            ≡⟨ cong (λ x → a₂ + x) (+-comm (b₁ + c₁) c₂) ⟩
                a₂ + (c₂ + (b₁ + c₁))
            ≡⟨ +-assoc a₂ c₂ (b₁ + c₁) ⟩
                (a₂ + c₂) + (b₁ + c₁)
            ∎

-- c +ℤ a = (c₁ + a₁ , c₂ + a₂)
-- c +ℤ b = (c₁ + b₁ , c₂ + b₂)
-- (c₁ + a₁) + (c₂ + b₂) ≡ (c₂ + a₂) + (c₁ + b₁)
+ℤ-rUniv : (a b c : ℤb) → a ≡ℤ b → (c +ℤ a) ≡ℤ (c +ℤ b)
+ℤ-rUniv (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) a₁+b₂≡a₂+b₁ = begin
        (c₁ + a₁) + (c₂ + b₂)
    ≡⟨ cong (λ x → (c₁ + a₁) + x) (+-comm c₂ b₂) ⟩
        (c₁ + a₁) + (b₂ + c₂)
    ≡⟨ sym (+-assoc c₁ a₁ (b₂ + c₂)) ⟩
        c₁ + (a₁ + (b₂ + c₂))
    ≡⟨ cong (λ x → c₁ + x) (+-assoc a₁ b₂ c₂) ⟩
        c₁ + ((a₁ + b₂) + c₂)
    ≡⟨ cong (λ x → c₁ + (x + c₂)) a₁+b₂≡a₂+b₁ ⟩
        c₁ + ((a₂ + b₁) + c₂)
    ≡⟨ +-comm c₁ ((a₂ + b₁) + c₂) ⟩
        ((a₂ + b₁) + c₂) + c₁
    ≡⟨ cong (λ x → x + c₁) (+-comm (a₂ + b₁) c₂) ⟩
        (c₂ + (a₂ + b₁)) + c₁
    ≡⟨ sym (+-assoc c₂ (a₂ + b₁) c₁) ⟩
        c₂ + ((a₂ + b₁) + c₁)
    ≡⟨ cong (λ x → c₂ + x) (sym (+-assoc a₂ b₁ c₁)) ⟩
        c₂ + (a₂ + (b₁ + c₁))
    ≡⟨ cong (λ x → c₂ + (a₂ + x)) (+-comm b₁ c₁) ⟩
        c₂ + (a₂ + (c₁ + b₁))
    ≡⟨ +-assoc c₂ a₂ (c₁ + b₁) ⟩
        (c₂ + a₂) + (c₁ + b₁)
    ∎

*ℤ-lUniv : (a b c : ℤb) → a ≡ℤ b → (a *ℤ c) ≡ℤ (b *ℤ c)
*ℤ-lUniv (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) a₁+b₂≡a₂+b₁ = lem
    where
        -- a *ℤ c = (a₁ * c₁ + a₂ * c₂ , a₁ * c₂ + a₂ * c₁)
        -- b *ℤ c = (b₁ * c₁ + b₂ * c₂ , b₁ * c₂ + b₂ * c₁)
        lem : ((a₁ * c₁) + (a₂ * c₂)) + ((b₁ * c₂) + (b₂ * c₁))
                ≡ ((a₁ * c₂) + (a₂ * c₁)) + ((b₁ * c₁) + (b₂ * c₂))
        lem = begin
                ((a₁ * c₁) + (a₂ * c₂)) + ((b₁ * c₂) + (b₂ * c₁))
            ≡⟨ cong (λ x → ((a₁ * c₁) + (a₂ * c₂)) + x) (+-comm (b₁ * c₂) (b₂ * c₁)) ⟩
                ((a₁ * c₁) + (a₂ * c₂)) + ((b₂ * c₁) + (b₁ * c₂))
            ≡⟨ sym (+-assoc (a₁ * c₁) (a₂ * c₂) ((b₂ * c₁) + (b₁ * c₂))) ⟩
                (a₁ * c₁) + ((a₂ * c₂) + ((b₂ * c₁) + (b₁ * c₂)))
            ≡⟨ cong (λ x → (a₁ * c₁) + x) (+-assoc (a₂ * c₂) (b₂ * c₁) (b₁ * c₂)) ⟩
                (a₁ * c₁) + (((a₂ * c₂) + (b₂ * c₁)) + (b₁ * c₂))
            ≡⟨ cong (λ x → (a₁ * c₁) + x) (cong (λ x → x + (b₁ * c₂)) (+-comm (a₂ * c₂) (b₂ * c₁))) ⟩
                (a₁ * c₁) + (((b₂ * c₁) + (a₂ * c₂)) + (b₁ * c₂))
            ≡⟨ cong (λ x → (a₁ * c₁) + x) (sym (+-assoc (b₂ * c₁) (a₂ * c₂) (b₁ * c₂))) ⟩
                (a₁ * c₁) + ((b₂ * c₁) + ((a₂ * c₂) + (b₁ * c₂)))
            ≡⟨ +-assoc (a₁ * c₁) (b₂ * c₁) ((a₂ * c₂) + (b₁ * c₂)) ⟩
                ((a₁ * c₁) + (b₂ * c₁)) + ((a₂ * c₂) + (b₁ * c₂))
            ≡⟨ cong (λ x → x + ((a₂ * c₂) + (b₁ * c₂))) (sym (+*-rDist a₁ b₂ c₁))  ⟩
                ((a₁ + b₂) * c₁) + ((a₂ * c₂) + (b₁ * c₂))
            ≡⟨ cong (λ x → ((a₁ + b₂) * c₁) + x) (sym (+*-rDist a₂ b₁ c₂)) ⟩
                ((a₁ + b₂) * c₁) + ((a₂ + b₁) * c₂)
            ≡⟨ cong (λ x → x + ((a₂ + b₁) * c₂)) (cong (λ x → x * c₁) a₁+b₂≡a₂+b₁) ⟩
                ((a₂ + b₁) * c₁) + ((a₂ + b₁) * c₂)
            ≡⟨ cong (λ x → ((a₂ + b₁) * c₁) + x) (cong (λ x → x * c₂) (sym a₁+b₂≡a₂+b₁)) ⟩
                ((a₂ + b₁) * c₁) + ((a₁ + b₂) * c₂)
            ≡⟨ cong (λ x → x + ((a₁ + b₂) * c₂)) (+*-rDist a₂ b₁ c₁) ⟩
                ((a₂ * c₁) + (b₁ * c₁)) + ((a₁ + b₂) * c₂)
            ≡⟨ cong (λ x → ((a₂ * c₁) + (b₁ * c₁)) + x) (+*-rDist a₁ b₂ c₂) ⟩
                ((a₂ * c₁) + (b₁ * c₁)) + ((a₁ * c₂) + (b₂ * c₂))
            ≡⟨ sym (+-assoc (a₂ * c₁) (b₁ * c₁) ((a₁ * c₂) + (b₂ * c₂))) ⟩
                (a₂ * c₁) + ((b₁ * c₁) + ((a₁ * c₂) + (b₂ * c₂)))
            ≡⟨ cong (λ x → (a₂ * c₁) + x) (+-assoc (b₁ * c₁) (a₁ * c₂) (b₂ * c₂)) ⟩
                (a₂ * c₁) + (((b₁ * c₁) + (a₁ * c₂)) + (b₂ * c₂))
            ≡⟨ cong (λ x → (a₂ * c₁) + x) (cong (λ x → x + (b₂ * c₂)) (+-comm (b₁ * c₁) (a₁ * c₂))) ⟩
                (a₂ * c₁) + (((a₁ * c₂) + (b₁ * c₁)) + (b₂ * c₂))
            ≡⟨ cong (λ x → (a₂ * c₁) + x) (sym (+-assoc (a₁ * c₂) (b₁ * c₁) (b₂ * c₂))) ⟩
                (a₂ * c₁) + ((a₁ * c₂) + ((b₁ * c₁) + (b₂ * c₂)))
            ≡⟨ +-assoc (a₂ * c₁) (a₁ * c₂) ((b₁ * c₁) + (b₂ * c₂)) ⟩
                ((a₂ * c₁) + (a₁ * c₂)) + ((b₁ * c₁) + (b₂ * c₂))
            ≡⟨ cong (λ x → x + ((b₁ * c₁) + (b₂ * c₂))) (+-comm (a₂ * c₁) (a₁ * c₂)) ⟩
                ((a₁ * c₂) + (a₂ * c₁)) + ((b₁ * c₁) + (b₂ * c₂))
            ∎

-- c *ℤ a = (c₁ * a₁) + (c₂ * a₂) , (c₁ * a₂) + (c₂ * a₁)
-- c *ℤ b = (c₁ * b₁) + (c₂ * b₂) , (c₁ * b₂) + (c₂ * b₁)
*ℤ-rUniv : (a b c : ℤb) → a ≡ℤ b → (c *ℤ a) ≡ℤ (c *ℤ b)
*ℤ-rUniv (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) a₁+b₂≡a₂+b₁ = begin
        ((c₁ * a₁) + (c₂ * a₂)) + ((c₁ * b₂) + (c₂ * b₁))
    ≡⟨ +-assoc ((c₁ * a₁) + (c₂ * a₂)) (c₁ * b₂) (c₂ * b₁) ⟩
        (((c₁ * a₁) + (c₂ * a₂)) + (c₁ * b₂)) + (c₂ * b₁)
    ≡⟨ cong (λ x → x + (c₂ * b₁)) (sym (+-assoc (c₁ * a₁) (c₂ * a₂) (c₁ * b₂))) ⟩
        ((c₁ * a₁) + ((c₂ * a₂) + (c₁ * b₂))) + (c₂ * b₁)
    ≡⟨ cong (λ z → ((c₁ * a₁) + z) + (c₂ * b₁)) (+-comm (c₂ * a₂) (c₁ * b₂)) ⟩
        ((c₁ * a₁) + ((c₁ * b₂) + (c₂ * a₂))) + (c₂ * b₁)
    ≡⟨ cong (λ z → z + (c₂ * b₁)) (+-assoc (c₁ * a₁) (c₁ * b₂) (c₂ * a₂)) ⟩
        (((c₁ * a₁) + (c₁ * b₂)) + (c₂ * a₂)) + (c₂ * b₁)
    ≡⟨ sym (+-assoc ((c₁ * a₁) + (c₁ * b₂)) (c₂ * a₂) (c₂ * b₁)) ⟩
        ((c₁ * a₁) + (c₁ * b₂)) + ((c₂ * a₂) + (c₂ * b₁))
    ≡⟨ cong (λ z → z + ((c₂ * a₂) + (c₂ * b₁))) (sym (+*-lDist a₁ b₂ c₁)) ⟩
        (c₁ * (a₁ + b₂)) + ((c₂ * a₂) + (c₂ * b₁))
    ≡⟨ cong (λ z → (c₁ * (a₁ + b₂)) + z) (sym (+*-lDist a₂ b₁ c₂)) ⟩
        (c₁ * (a₁ + b₂)) + (c₂ * (a₂ + b₁))
    ≡⟨ cong (λ z → (c₁ * z) + (c₂ * (a₂ + b₁))) a₁+b₂≡a₂+b₁ ⟩
        (c₁ * (a₂ + b₁)) + (c₂ * (a₂ + b₁))
    ≡⟨ cong (λ z → (c₁ * (a₂ + b₁)) + (c₂ * z)) (sym a₁+b₂≡a₂+b₁) ⟩
        (c₁ * (a₂ + b₁)) + (c₂ * (a₁ + b₂))
    ≡⟨ cong (λ z → z + (c₂ * (a₁ + b₂))) (+*-lDist a₂ b₁ c₁) ⟩
        ((c₁ * a₂) + (c₁ * b₁)) + (c₂ * (a₁ + b₂))
    ≡⟨ cong (λ z → ((c₁ * a₂) + (c₁ * b₁)) + z) (+*-lDist a₁ b₂ c₂) ⟩
        ((c₁ * a₂) + (c₁ * b₁)) + ((c₂ * a₁) + (c₂ * b₂))
    ≡⟨ sym (+-assoc (c₁ * a₂) (c₁ * b₁) ((c₂ * a₁) + (c₂ * b₂))) ⟩
        (c₁ * a₂) + ((c₁ * b₁) + ((c₂ * a₁) + (c₂ * b₂)))
    ≡⟨ cong (λ z → (c₁ * a₂) + z) (+-assoc (c₁ * b₁) (c₂ * a₁) (c₂ * b₂)) ⟩
        (c₁ * a₂) + (((c₁ * b₁) + (c₂ * a₁)) + (c₂ * b₂))
    ≡⟨ cong (λ z → (c₁ * a₂) + (z + (c₂ * b₂))) (+-comm (c₁ * b₁) (c₂ * a₁)) ⟩
        (c₁ * a₂) + (((c₂ * a₁) + (c₁ * b₁)) + (c₂ * b₂))
    ≡⟨ cong (λ z → (c₁ * a₂) + z) (sym (+-assoc (c₂ * a₁) (c₁ * b₁) (c₂ * b₂))) ⟩
        (c₁ * a₂) + ((c₂ * a₁) + ((c₁ * b₁) + (c₂ * b₂)))
    ≡⟨ +-assoc (c₁ * a₂) (c₂ * a₁) ((c₁ * b₁) + (c₂ * b₂)) ⟩
        ((c₁ * a₂) + (c₂ * a₁)) + ((c₁ * b₁) + (c₂ * b₂))
    ∎

+ℤ-rUnit : (a b : ℕ) → ((a , b) +ℤ (zero , zero)) ≡ (a , b)
+ℤ-rUnit a b = begin
        (a , b) +ℤ (zero , zero)
    ≡⟨ refl ⟩
        (a + zero , b + zero)
    ≡⟨ cong (λ x → x , (b + zero)) (+-rUnit a) ⟩
        (a , b + zero)
    ≡⟨ cong (λ x → a , x) (+-rUnit b) ⟩
        (a , b)
    ∎

+ℤ-lUnit : (a b : ℕ) → ((zero , zero) +ℤ (a , b)) ≡ (a , b)
+ℤ-lUnit a b = begin
        (zero , zero) +ℤ (a , b)
    ≡⟨ refl ⟩
        (zero + a , zero + b)
    ≡⟨ refl ⟩
        (a , b)
    ∎

-- (a , b) *ℤ (succ zero , zero) = (a * succ zero + b * zero , a * zero + b * succ zero)
-- a + (a * zero + b * succ zero) = b + (a * succ zero + b * zero)
*ℤ-rUnit : (a b : ℕ) → ((a , b) *ℤ (succ zero , zero)) ≡ (a , b)
*ℤ-rUnit a b = begin
        ((a * succ zero) + (b * zero) , ((a * zero) + (b * succ zero)))
    ≡⟨ cong (λ x → x , ((a * zero) + (b * succ zero))) lem1 ⟩
        (a , ((a * zero) + (b * succ zero)))
    ≡⟨ cong (λ x → a , x) lem2 ⟩
        (a , b)
    ∎
    where
        lem1 : (a * succ zero) + (b * zero) ≡ a
        lem1 = begin
                (a * succ zero) + (b * zero)
            ≡⟨ cong (λ x → x + (b * zero)) (*-rUnit a) ⟩
                a + (b * zero)
            ≡⟨ cong (λ x → a + x) (*-rAbsorp b) ⟩
                a + zero
            ≡⟨ +-rUnit a ⟩
                a
            ∎
        lem2 : (a * zero) + (b * succ zero) ≡ b
        lem2 = begin
                (a * zero) + (b * succ zero)
            ≡⟨ cong (λ x → (a * zero) + x) (*-rUnit b) ⟩
                (a * zero) + b
            ≡⟨ cong (λ x → x + b) (*-rAbsorp a) ⟩
                zero + b
            ≡⟨ refl ⟩
                b
            ∎

-- ((succ zero * a) + (zero * b) , (succ zero * b) + (zero * a))
*ℤ-lUnit : (a b : ℕ) → ((succ zero , zero) *ℤ (a , b)) ≡ (a , b)
*ℤ-lUnit a b = begin
        ((succ zero * a) + (zero * b) , (succ zero * b) + (zero * a))
    ≡⟨ cong (λ x → x , ((succ zero * b) + (zero * a))) lem1 ⟩
        (a , (succ zero * b) + (zero * a))
    ≡⟨ cong (λ x → a , x) lem2 ⟩
        (a , b)
    ∎
    where
        lem1 : (succ zero * a) + (zero * b) ≡ a
        lem1 = begin
                (succ zero * a) + (zero * b)
            ≡⟨ cong (λ x → x + (zero * b)) (*-lUnit a) ⟩
                a + (zero * b)
            ≡⟨ cong (λ x → a + x) refl ⟩
                a + zero
            ≡⟨ +-rUnit a ⟩
                a
            ∎
        lem2 : (succ zero * b) + (zero * a) ≡ b
        lem2 = begin
                (succ zero * b) + (zero * a)
            ≡⟨ cong (λ x → x + (zero * a)) (*-lUnit b) ⟩
                b + (zero * a)
            ≡⟨ cong (λ x → b + x) refl ⟩
                b + zero
            ≡⟨ +-rUnit b ⟩
                b
            ∎

-- (b +ℤ c) = (b₁ + c₁) , (b₂ + c₂)
-- a +ℤ (b +ℤ c) = a₁ + (b₁ + c₁) , a₂ + (b₂ + c₂)
-- (a +ℤ b) = a₁ + b₁ , a₂ + b₂
-- (a +ℤ b) + c = (a₁ + b₁) + c₁ , (a₂ + b₂) + c₂
-- (a₁ + (b₁ + c₁)) + ((a₂ + b₂) + c₂) ≡ (a₂ + (b₂ + c₂)) + ((a₁ + b₁) + c₁)
+ℤ-assoc : (a b c : ℤb) → (a +ℤ (b +ℤ c)) ≡ℤ ((a +ℤ b) +ℤ c)
+ℤ-assoc (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) = begin
        (a₁ + (b₁ + c₁)) + ((a₂ + b₂) + c₂)
    ≡⟨ +-comm (a₁ + (b₁ + c₁)) ((a₂ + b₂) + c₂) ⟩
        ((a₂ + b₂) + c₂) + (a₁ + (b₁ + c₁))
    ≡⟨ cong (λ x → x + (a₁ + (b₁ + c₁))) (sym (+-assoc a₂ b₂ c₂)) ⟩
        (a₂ + (b₂ + c₂)) + (a₁ + (b₁ + c₁))
    ≡⟨ cong (λ x → (a₂ + (b₂ + c₂)) + x) (+-assoc a₁ b₁ c₁) ⟩
        (a₂ + (b₂ + c₂)) + ((a₁ + b₁) + c₁)
    ∎

-- a +ℤ b = a + c , b + d
-- b +ℤ a = c + a , d + b
-- (a + c) + (d + b) = (b + d) + (c + a)
+ℤ-comm : (a b : ℤb) → (a +ℤ b) ≡ℤ (b +ℤ a)
+ℤ-comm (a , b) (c , d) = begin
        (a + c) + (d + b)
    ≡⟨ +-comm (a + c) (d + b) ⟩
        (d + b) + (a + c)
    ≡⟨ cong (λ x → x + (a + c)) (+-comm d b) ⟩
        (b + d) + (a + c)
    ≡⟨ cong (λ x → (b + d) + x) (+-comm a c) ⟩
        (b + d) + (c + a)
    ∎

-- b *ℤ c = (b₁ * c₁) + (b₂ * c₂) , (b₁ * c₂) + (b₂ * c₁)
-- a *ℤ (b *ℤ c) = (a₁ * ((b₁ * c₁) + (b₂ * c₂))) + (a₂ * ((b₁ * c₂) + (b₂ * c₁)))
--               , (a₁ * ((b₁ * c₂) + (b₂ * c₁))) + (a₂ * ((b₁ * c₁) + (b₂ * c₂)))
-- a *ℤ b = (a₁ * b₁) + (a₂ * b₂) , (a₁ * b₂) + (a₂ * b₁)
-- (a *ℤ b) *ℤ c = (((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) + (a₂ * b₁)) * c₂)
--               , (((a₁ * b₂) + (a₂ * b₁)) * c₁) + (((a₁ * b₁) + (a₂ * b₂)) * c₂)
-- (a₁ * ((b₁ * c₁) + (b₂ * c₂))) + (a₂ * ((b₁ * c₂) + (b₂ * c₁)))
-- + (((a₁ * b₂) + (a₂ * b₁)) * c₁) + (((a₁ * b₁) + (a₂ * b₂)) * c₂)
-- ≡
-- (a₁ * ((b₁ * c₂) + (b₂ * c₁))) + (a₂ * ((b₁ * c₁) + (b₂ * c₂)))
-- + (((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) + (a₂ * b₁)) * c₂)
*ℤ-assoc : (a b c : ℤb) → (a *ℤ (b *ℤ c)) ≡ℤ ((a *ℤ b) *ℤ c)
*ℤ-assoc a@(a₁ , a₂) b@(b₁ , b₂) c@(c₁ , c₂) = ≡ℤ-≡ (begin
        a *ℤ (b *ℤ c)
    ≡⟨ cong (λ x → a *ℤ x) refl ⟩
        a *ℤ ((b₁ * c₁) + (b₂ * c₂) , (b₁ * c₂) + (b₂ * c₁))
    ≡⟨ refl ⟩
        ((a₁ * ((b₁ * c₁) + (b₂ * c₂))) + (a₂ * ((b₁ * c₂) + (b₂ * c₁))) ,
            ((a₁ * ((b₁ * c₂) + (b₂ * c₁))) + (a₂ * ((b₁ * c₁) + (b₂ * c₂)))))
    ≡⟨ cong (λ z → z , (((a₁ * ((b₁ * c₂) + (b₂ * c₁))) + (a₂ * ((b₁ * c₁) + (b₂ * c₂)))))) lem1 ⟩
        ((((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) + (a₂ * b₁)) * c₂)) ,
            ((a₁ * ((b₁ * c₂) + (b₂ * c₁))) + (a₂ * ((b₁ * c₁) + (b₂ * c₂))))
    ≡⟨ cong (λ z → (((((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) + (a₂ * b₁)) * c₂))) , z) lem2 ⟩
        ((((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) + (a₂ * b₁)) * c₂)) ,
         ((((a₁ * b₁) + (a₂ * b₂)) * c₂) + (((a₁ * b₂) + (a₂ * b₁)) * c₁))
    ≡⟨ refl ⟩
        ((a₁ * b₁) + (a₂ * b₂) , (a₁ * b₂) + (a₂ * b₁)) *ℤ c
    ≡⟨ cong (λ z → z *ℤ c) t-lem ⟩
        (a *ℤ b) *ℤ c
    ∎)
    where
        t-lem : ((a₁ * b₁) + (a₂ * b₂) , (a₁ * b₂) + (a₂ * b₁)) ≡ (a *ℤ b)
        t-lem = refl
        lem1 : ((a₁ * ((b₁ * c₁) + (b₂ * c₂))) + (a₂ * ((b₁ * c₂) + (b₂ * c₁)))) ≡
                ((((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) + (a₂ * b₁)) * c₂))
        lem1 = begin
                ((a₁ * ((b₁ * c₁) + (b₂ * c₂))) + (a₂ * ((b₁ * c₂) + (b₂ * c₁))))
            ≡⟨ cong (λ z → z + (a₂ * ((b₁ * c₂) + (b₂ * c₁)))) (+*-lDist (b₁ * c₁) (b₂ * c₂) a₁) ⟩
                ((a₁ * (b₁ * c₁)) + (a₁ * (b₂ * c₂))) + (a₂ * ((b₁ * c₂) + (b₂ * c₁)))
            ≡⟨ cong (λ z → (((a₁ * (b₁ * c₁)) + (a₁ * (b₂ * c₂)))) + z) (+*-lDist (b₁ * c₂) (b₂ * c₁) a₂) ⟩
                ((a₁ * (b₁ * c₁)) + (a₁ * (b₂ * c₂))) + ((a₂ * (b₁ * c₂)) + (a₂ * (b₂ * c₁)))
            ≡⟨ cong (λ z → (((a₁ * (b₁ * c₁)) + (a₁ * (b₂ * c₂)))) + z) (+-comm (a₂ * (b₁ * c₂)) (a₂ * (b₂ * c₁))) ⟩
                ((a₁ * (b₁ * c₁)) + (a₁ * (b₂ * c₂))) + ((a₂ * (b₂ * c₁)) + (a₂ * (b₁ * c₂)))
            ≡⟨ sym (+-assoc (a₁ * (b₁ * c₁)) (a₁ * (b₂ * c₂)) ((a₂ * (b₂ * c₁)) + (a₂ * (b₁ * c₂)))) ⟩
                (a₁ * (b₁ * c₁)) + ((a₁ * (b₂ * c₂)) + (((a₂ * (b₂ * c₁)) + (a₂ * (b₁ * c₂)))))
            ≡⟨ cong (λ z → (a₁ * (b₁ * c₁)) + z) (+-assoc (a₁ * (b₂ * c₂)) (a₂ * (b₂ * c₁)) (a₂ * (b₁ * c₂))) ⟩
                (a₁ * (b₁ * c₁)) + (((a₁ * (b₂ * c₂)) + (a₂ * (b₂ * c₁))) + (a₂ * (b₁ * c₂)))
            ≡⟨ cong (λ z → (a₁ * (b₁ * c₁)) + (z + (a₂ * (b₁ * c₂)))) (+-comm (a₁ * (b₂ * c₂)) (a₂ * (b₂ * c₁))) ⟩
                (a₁ * (b₁ * c₁)) + (((a₂ * (b₂ * c₁)) + (a₁ * (b₂ * c₂))) + (a₂ * (b₁ * c₂)))
            ≡⟨ cong (λ z → (a₁ * (b₁ * c₁)) + z) (sym (+-assoc (a₂ * (b₂ * c₁)) (a₁ * (b₂ * c₂)) (a₂ * (b₁ * c₂)))) ⟩
                (a₁ * (b₁ * c₁)) + ((a₂ * (b₂ * c₁)) + ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂))))
            ≡⟨ +-assoc (a₁ * (b₁ * c₁)) (a₂ * (b₂ * c₁)) ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂))) ⟩
                ((a₁ * (b₁ * c₁)) + (a₂ * (b₂ * c₁))) + ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂)))
            ≡⟨ cong (λ z → (z + (a₂ * (b₂ * c₁))) + ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂)))) (*-assoc a₁ b₁ c₁) ⟩
                (((a₁ * b₁) * c₁) + (a₂ * (b₂ * c₁))) + ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂)))
            ≡⟨ cong (λ z → (((a₁ * b₁) * c₁) + z) + ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂)))) (*-assoc a₂ b₂ c₁) ⟩
                (((a₁ * b₁) * c₁) + ((a₂ * b₂) * c₁)) + ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂)))
            ≡⟨ cong (λ z → z + ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂)))) (sym (+*-rDist (a₁ * b₁) (a₂ * b₂) c₁)) ⟩
                (((a₁ * b₁) + (a₂ * b₂)) * c₁) + ((a₁ * (b₂ * c₂)) + (a₂ * (b₁ * c₂)))
            ≡⟨ cong (λ z → ((((a₁ * b₁) + (a₂ * b₂)) * c₁)) + (z + (a₂ * (b₁ * c₂)))) (*-assoc a₁ b₂ c₂) ⟩
                (((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) * c₂) + (a₂ * (b₁ * c₂)))
            ≡⟨ cong (λ z → (((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) * c₂) + z)) (*-assoc a₂ b₁ c₂) ⟩
                (((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) * c₂) + ((a₂ * b₁) * c₂))
            ≡⟨ cong (λ z → ((((a₁ * b₁) + (a₂ * b₂)) * c₁)) + z) (sym (+*-rDist (a₁ * b₂) (a₂ * b₁) c₂)) ⟩
                (((a₁ * b₁) + (a₂ * b₂)) * c₁) + (((a₁ * b₂) + (a₂ * b₁)) * c₂)
            ∎
        lem2 : ((a₁ * ((b₁ * c₂) + (b₂ * c₁))) + (a₂ * ((b₁ * c₁) + (b₂ * c₂)))) ≡
                ((((a₁ * b₁) + (a₂ * b₂)) * c₂) + (((a₁ * b₂) + (a₂ * b₁)) * c₁))
        lem2 = begin
                (a₁ * ((b₁ * c₂) + (b₂ * c₁))) + (a₂ * ((b₁ * c₁) + (b₂ * c₂)))
            ≡⟨ cong (λ x → x + (a₂ * ((b₁ * c₁) + (b₂ * c₂)))) (+*-lDist (b₁ * c₂) (b₂ * c₁) a₁) ⟩
                ((a₁ * (b₁ * c₂)) + (a₁ * (b₂ * c₁))) + (a₂ * ((b₁ * c₁) + (b₂ * c₂)))
            ≡⟨ cong (λ x → (((a₁ * (b₁ * c₂)) + (a₁ * (b₂ * c₁)))) + x) (+*-lDist (b₁ * c₁) (b₂ * c₂) a₂) ⟩
                ((a₁ * (b₁ * c₂)) + (a₁ * (b₂ * c₁))) + ((a₂ * (b₁ * c₁)) + (a₂ * (b₂ * c₂)))
            ≡⟨ cong (λ x → (x + ((a₁ * (b₂ * c₁)))) + (((a₂ * (b₁ * c₁)) + (a₂ * (b₂ * c₂))))) (*-assoc a₁ b₁ c₂) ⟩
                (((a₁ * b₁) * c₂) + (a₁ * (b₂ * c₁))) + ((a₂ * (b₁ * c₁)) + (a₂ * (b₂ * c₂)))
            ≡⟨ cong (λ x → ((((a₁ * b₁) * c₂)) + x) + (((a₂ * (b₁ * c₁)) + (a₂ * (b₂ * c₂))))) (*-assoc a₁ b₂ c₁) ⟩
                (((a₁ * b₁) * c₂) + ((a₁ * b₂) * c₁)) + ((a₂ * (b₁ * c₁)) + (a₂ * (b₂ * c₂)))
            ≡⟨ cong (λ x → ((((a₁ * b₁) * c₂) + ((a₁ * b₂) * c₁))) + (x + (a₂ * (b₂ * c₂)))) (*-assoc a₂ b₁ c₁) ⟩
                (((a₁ * b₁) * c₂) + ((a₁ * b₂) * c₁)) + (((a₂ * b₁) * c₁) + (a₂ * (b₂ * c₂)))
            ≡⟨ cong (λ x → ((((a₁ * b₁) * c₂) + ((a₁ * b₂) * c₁))) + (((a₂ * b₁) * c₁) + x)) (*-assoc a₂ b₂ c₂) ⟩
                (((a₁ * b₁) * c₂) + ((a₁ * b₂) * c₁)) + (((a₂ * b₁) * c₁) + ((a₂ * b₂) * c₂))
            ≡⟨ sym (+-assoc ((a₁ * b₁) * c₂) ((a₁ * b₂) * c₁) (((a₂ * b₁) * c₁) + ((a₂ * b₂) * c₂))) ⟩
                ((a₁ * b₁) * c₂) + (((a₁ * b₂) * c₁) + (((a₂ * b₁) * c₁) + ((a₂ * b₂) * c₂)))
            ≡⟨ cong (λ x → (((a₁ * b₁) * c₂)) + x) (+-assoc ((a₁ * b₂) * c₁) ((a₂ * b₁) * c₁) ((a₂ * b₂) * c₂)) ⟩
                ((a₁ * b₁) * c₂) + ((((a₁ * b₂) * c₁) + ((a₂ * b₁) * c₁)) + ((a₂ * b₂) * c₂))
            ≡⟨ cong (λ x → (((a₁ * b₁) * c₂)) + x) (+-comm (((a₁ * b₂) * c₁) + ((a₂ * b₁) * c₁)) ((a₂ * b₂) * c₂)) ⟩
                ((a₁ * b₁) * c₂) + (((a₂ * b₂) * c₂) + (((a₁ * b₂) * c₁) + ((a₂ * b₁) * c₁)))
            ≡⟨ +-assoc ((a₁ * b₁) * c₂) ((a₂ * b₂) * c₂) (((a₁ * b₂) * c₁) + ((a₂ * b₁) * c₁)) ⟩
                (((a₁ * b₁) * c₂) + ((a₂ * b₂) * c₂)) + (((a₁ * b₂) * c₁) + ((a₂ * b₁) * c₁))
            ≡⟨ cong (λ x → x + (((a₁ * b₂) * c₁) + ((a₂ * b₁) * c₁))) (sym (+*-rDist (a₁ * b₁) (a₂ * b₂) c₂)) ⟩
                (((a₁ * b₁) + (a₂ * b₂)) * c₂) + (((a₁ * b₂) * c₁) + ((a₂ * b₁) * c₁))
            ≡⟨ cong (λ x → ((((a₁ * b₁) + (a₂ * b₂)) * c₂)) + x) (sym (+*-rDist (a₁ * b₂) (a₂ * b₁) c₁)) ⟩
                (((a₁ * b₁) + (a₂ * b₂)) * c₂) + (((a₁ * b₂) + (a₂ * b₁)) * c₁)
            ∎


-- a *ℤ b = a₁ * b₁ + a₂ * b₂ , a₁ * b₂ + a₂ * b₁
-- b *ℤ a = b₁ * a₁ + b₂ * a₂ , b₁ * a₂ + b₂ * a₁
*ℤ-comm : (a b : ℤb) → (a *ℤ b) ≡ℤ (b *ℤ a)
*ℤ-comm (a₁ , a₂) (b₁ , b₂) = begin
        ((a₁ * b₁) + (a₂ * b₂)) + ((b₁ * a₂) + (b₂ * a₁))
    ≡⟨ +-comm ((a₁ * b₁) + (a₂ * b₂)) ((b₁ * a₂) + (b₂ * a₁)) ⟩
        ((b₁ * a₂) + (b₂ * a₁)) + ((a₁ * b₁) + (a₂ * b₂))
    ≡⟨ cong (λ z → z + ((a₁ * b₁) + (a₂ * b₂))) (+-comm (b₁ * a₂) (b₂ * a₁)) ⟩
        ((b₂ * a₁) + (b₁ * a₂)) + ((a₁ * b₁) + (a₂ * b₂))
    ≡⟨ cong (λ z → (z + (b₁ * a₂)) + ((a₁ * b₁) + (a₂ * b₂))) (*-comm b₂ a₁) ⟩
        ((a₁ * b₂) + (b₁ * a₂)) + ((a₁ * b₁) + (a₂ * b₂))
    ≡⟨ cong (λ z → ((a₁ * b₂) + z) + ((a₁ * b₁) + (a₂ * b₂))) (*-comm b₁ a₂) ⟩
        ((a₁ * b₂) + (a₂ * b₁)) + ((a₁ * b₁) + (a₂ * b₂))
    ≡⟨ cong (λ z → ((a₁ * b₂) + (a₂ * b₁)) + (z + (a₂ * b₂))) (*-comm a₁ b₁) ⟩
        ((a₁ * b₂) + (a₂ * b₁)) + ((b₁ * a₁) + (a₂ * b₂))
    ≡⟨ cong (λ z → ((a₁ * b₂) + (a₂ * b₁)) + ((b₁ * a₁) + z)) (*-comm a₂ b₂) ⟩
        ((a₁ * b₂) + (a₂ * b₁)) + ((b₁ * a₁) + (b₂ * a₂))
    ∎

ℕ-ℤ : ℕ → ℤb
ℕ-ℤ n = (n , zero)

ℕ-ℤ-monic : (m n : ℕ) → ℕ-ℤ m ≡ℤ ℕ-ℤ n → m ≡ n
ℕ-ℤ-monic m n m+0≡0+n = begin
        m
    ≡⟨ sym (+-rUnit m) ⟩
        m + zero
    ≡⟨ m+0≡0+n ⟩
        zero + n
    ≡⟨ refl ⟩
        n
    ∎

-- (n , zero) +ℤ (zero , n) = n + zero , zero + n
-- (n + zero) + zero = (zero + n) + zero
+ℤ-invℕ : (n : ℕ) → ((n , zero) +ℤ (zero , n)) ≡ℤ (zero , zero)
+ℤ-invℕ n = begin
        (n + zero) + zero
    ≡⟨ cong (λ x → x + zero) (+-comm n zero) ⟩
        (zero + n) + zero
    ∎

-- (a , b) +ℤ (b , a) = a + b , b + a
-- (a + b) + zero = (b + a) + zero
+ℤ-inv : (a : ℤb) → ∃ λ b → (a +ℤ b) ≡ℤ (zero , zero)
+ℤ-inv (a , b) = (b , a) , (begin
        (a + b) + zero
    ≡⟨ cong (λ x → x + zero) (+-comm a b) ⟩
        (b + a) + zero
    ∎)

-ℤ_ : ℤb → ℤb
-ℤ (a , b) = (b , a)

_-ℤ_ : ℤb → ℤb → ℤb
a -ℤ b = a +ℤ (-ℤ b)

-ℤ-inv : (a : ℤb) → (a -ℤ a) ≡ℤ (zero , zero)
-ℤ-inv (a , b) = begin
        (a + b) + zero
    ≡⟨ cong (λ x → x + zero) (+-comm a b) ⟩
        (b + a) + zero
    ∎

_≤ℤ_ : ℤb → ℤb → Set
a ≤ℤ b = ∃ λ l → (a +ℤ (l , zero)) ≡ℤ b

≤ℤ-refl : (a : ℤb) → a ≤ℤ a
≤ℤ-refl (a , b) = zero , ≡ℤ-≡ (+ℤ-rUnit a b)

-- p : (a₁ , a₂) +ℤ (x , zero) ≡ℤ (b₁ , b₂)
-- (a₁ + x , a₂ + zero) ≡ℤ (b₁ , b₂)
-- (a₁ + x) + b₂ = (a₂ + zero) + b₁
-- q : (b₁ , b₂) +ℤ (x , zero) ≡ℤ (c₁ , c₂)
-- (b₁ + y , b₂ + zero) ≡ℤ (c₁ , c₂)
-- (b₁ + y) + c₂ = (b₂ + zero) + c₁
-- goal : (a₁ , a₂) +ℤ (z , zero) ≡ℤ (c₁ , c₂)
-- (a₁ + z , a₂ + zero) ≡ℤ (c₁ , c₂)
-- (a₁ + z) + c₂ ≡ (a₂ + zero) + c₁
≤ℤ-trans : (a b c : ℤb) → a ≤ℤ b → b ≤ℤ c → a ≤ℤ c
≤ℤ-trans (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) (x , p) (y , q) = (x + y) ,
    +-rCancel ((a₁ + (x + y)) + c₂) ((a₂ + zero) + c₁) b₂ (begin
            ((a₁ + (x + y)) + c₂) + b₂
        ≡⟨ cong (λ z → z + b₂) (sym (+-assoc a₁ (x + y) c₂)) ⟩
            (a₁ + ((x + y) + c₂)) + b₂
        ≡⟨ sym (+-assoc a₁ ((x + y) + c₂) b₂) ⟩
            a₁ + (((x + y) + c₂) + b₂)
        ≡⟨ cong (λ z → a₁ + z) (sym (+-assoc (x + y) c₂ b₂)) ⟩
            a₁ + ((x + y) + (c₂ + b₂))
        ≡⟨ cong (λ z → a₁ + ((x + y) + z)) (+-comm c₂ b₂) ⟩
            a₁ + ((x + y) + (b₂ + c₂))
        ≡⟨ cong (λ z → a₁ + z) (sym (+-assoc x y (b₂ + c₂))) ⟩
            a₁ + (x + (y + (b₂ + c₂)))
        ≡⟨ cong (λ z → a₁ + (x + z)) (+-assoc y b₂ c₂) ⟩
            a₁ + (x + ((y + b₂) + c₂))
        ≡⟨ cong (λ z → a₁ + (x + (z + c₂))) (+-comm y b₂) ⟩
            a₁ + (x + ((b₂ + y) + c₂))
        ≡⟨ cong (λ z → a₁ + (x + z)) (sym (+-assoc b₂ y c₂)) ⟩
            a₁ + (x + (b₂ + (y + c₂)))
        ≡⟨ +-assoc a₁ x (b₂ + (y + c₂)) ⟩
            ((a₁ + x) + (b₂ + (y + c₂)))
        ≡⟨ +-assoc (a₁ + x) b₂ (y + c₂) ⟩
            ((a₁ + x) + b₂) + (y + c₂)
        ≡⟨ cong (λ z → z + (y + c₂)) p ⟩
            ((a₂ + zero) + b₁) + (y + c₂)
        ≡⟨ sym (+-assoc (a₂ + zero) b₁ (y + c₂)) ⟩
            (a₂ + zero) + (b₁ + (y + c₂))
        ≡⟨ cong (λ z → (a₂ + zero) + z) (+-assoc b₁ y c₂) ⟩
            (a₂ + zero) + ((b₁ + y) + c₂)
        ≡⟨ cong (λ z → (a₂ + zero) + z) q ⟩
            (a₂ + zero) + ((b₂ + zero) + c₁)
        ≡⟨ cong (λ z → (a₂ + zero) + z) (+-comm (b₂ + zero) c₁) ⟩
            (a₂ + zero) + (c₁ + (b₂ + zero))
        ≡⟨ cong (λ z → (a₂ + zero) + (c₁ + z)) (+-rUnit b₂) ⟩
            (a₂ + zero) + (c₁ + b₂)
        ≡⟨ +-assoc (a₂ + zero) c₁ b₂ ⟩
            ((a₂ + zero) + c₁) + b₂
        ∎)

-- p : (a₁ + x , a₂ + zero) ≡ℤ (b₁ , b₂)
-- (a₁ + x) + b₂ ≡ (a₂ + zero) + b₁
-- q : (b₁ + y , b₂ + zero) ≡ℤ (a₁ , a₂)
-- (b₁ + y) + a₂ ≡ (b₂ + zero) + a₁
≤ℤ-antisym : (a b : ℤb) → a ≤ℤ b → b ≤ℤ a → a ≡ℤ b
≤ℤ-antisym (a₁ , a₂) (b₁ , b₂) (x , p) (y , q) = begin
        a₁ + b₂
    ≡⟨ sym (+-rUnit (a₁ + b₂)) ⟩
        (a₁ + b₂) + zero
    ≡⟨ cong (λ z → (a₁ + b₂) + z) (sym x≡0) ⟩
        (a₁ + b₂) + x
    ≡⟨ sym (+-assoc a₁ b₂ x) ⟩
        a₁ + (b₂ + x)
    ≡⟨ cong (λ z → a₁ + z) (+-comm b₂ x) ⟩
        a₁ + (x + b₂)
    ≡⟨ +-assoc a₁ x b₂ ⟩
        (a₁ + x) + b₂
    ≡⟨ p ⟩
        (a₂ + zero) + b₁
    ≡⟨ cong (λ z → z + b₁) (+-rUnit a₂) ⟩
        a₂ + b₁
    ∎
    where
        x≡0 : x ≡ zero
        x≡0 = +-lZero x y (+-lCancel (x + y) zero ((a₁ + b₂) + a₂) (begin
                ((a₁ + b₂) + a₂) + (x + y)
            ≡⟨ sym (+-assoc (a₁ + b₂) a₂ (x + y)) ⟩
                (a₁ + b₂) + (a₂ + (x + y))
            ≡⟨ cong (λ x₁ → (a₁ + b₂) + x₁) (+-assoc a₂ x y) ⟩
                (a₁ + b₂) + ((a₂ + x) + y)
            ≡⟨ cong (λ z → (a₁ + b₂) + (z + y)) (+-comm a₂ x) ⟩
                (a₁ + b₂) + ((x + a₂) + y)
            ≡⟨ cong (λ z → (a₁ + b₂) + z) (sym (+-assoc x a₂ y)) ⟩
                (a₁ + b₂) + (x + (a₂ + y))
            ≡⟨ +-assoc (a₁ + b₂) x (a₂ + y) ⟩
                ((a₁ + b₂) + x) + (a₂ + y)
            ≡⟨ cong (λ z → z + (a₂ + y)) (sym (+-assoc a₁ b₂ x)) ⟩
                (a₁ + (b₂ + x)) + (a₂ + y)
            ≡⟨ cong (λ z → (a₁ + z) + (a₂ + y)) (+-comm b₂ x) ⟩
                (a₁ + (x + b₂)) + (a₂ + y)
            ≡⟨ cong (λ z → z + (a₂ + y)) (+-assoc a₁ x b₂) ⟩
                ((a₁ + x) + b₂) + (a₂ + y)
            ≡⟨ cong (λ z → z + (a₂ + y)) p ⟩
                ((a₂ + zero) + b₁) + (a₂ + y)
            ≡⟨ sym (+-assoc (a₂ + zero) b₁ (a₂ + y)) ⟩
                (a₂ + zero) + (b₁ + (a₂ + y))
            ≡⟨ cong (λ z → (a₂ + zero) + (b₁ + z)) (+-comm a₂ y) ⟩
                (a₂ + zero) + (b₁ + (y + a₂))
            ≡⟨ cong (λ z → (a₂ + zero) + z) (+-assoc b₁ y a₂) ⟩
                (a₂ + zero) + ((b₁ + y) + a₂)
            ≡⟨ cong (λ z → (a₂ + zero) + z) q ⟩
                (a₂ + zero) + ((b₂ + zero) + a₁)
            ≡⟨ +-comm (a₂ + zero) ((b₂ + zero) + a₁) ⟩
                ((b₂ + zero) + a₁) + (a₂ + zero)
            ≡⟨ cong (λ z → z + (a₂ + zero)) (+-comm (b₂ + zero) a₁) ⟩
                (a₁ + (b₂ + zero)) + (a₂ + zero)
            ≡⟨ cong (λ z → (a₁ + z) + (a₂ + zero)) (+-rUnit b₂) ⟩
                (a₁ + b₂) + (a₂ + zero)
            ≡⟨ +-assoc (a₁ + b₂) a₂ zero ⟩
                ((a₁ + b₂) + a₂) + zero
            ∎))

-- (a₁ , a₂) ≤ℤ (b₁ , b₂)
-- (a₁ + l , a₂ + zero) ≡ℤ (b₁ , b₂)
-- (a₁ + l) + b₂ ≡ (a₂ + zero) + b₁
≤ℤ-all : (a b : ℤb) → a ≤ℤ b ⊎ b ≤ℤ a
≤ℤ-all a@(a₁ , a₂) b@(b₁ , b₂) = S.map lem1 lem2 (≤-all (a₁ + b₂) (a₂ + b₁))
    where
        lem1 : (a₁ + b₂) ≤ (a₂ + b₁) → a ≤ℤ b
        lem1 (x , p) = x , (begin
                (a₁ + x) + b₂
            ≡⟨ sym (+-assoc a₁ x b₂) ⟩
                a₁ + (x + b₂)
            ≡⟨ cong (λ z → a₁ + z) (+-comm x b₂) ⟩
                a₁ + (b₂ + x)
            ≡⟨ +-assoc a₁ b₂ x ⟩
                (a₁ + b₂) + x
            ≡⟨ p ⟩
                a₂ + b₁
            ≡⟨ cong (λ z → z + b₁) (sym (+-rUnit a₂)) ⟩
                (a₂ + zero) + b₁
            ∎)
        lem2 : (a₂ + b₁) ≤ (a₁ + b₂) → b ≤ℤ a
        lem2 (x , p) = x , (begin
                (b₁ + x) + a₂
            ≡⟨ sym (+-assoc b₁ x a₂) ⟩
                b₁ + (x + a₂)
            ≡⟨ cong (λ z → b₁ + z) (+-comm x a₂) ⟩
                b₁ + (a₂ + x)
            ≡⟨ +-assoc b₁ a₂ x ⟩
                (b₁ + a₂) + x
            ≡⟨ cong (λ z → z + x) (+-comm b₁ a₂) ⟩
                (a₂ + b₁) + x
            ≡⟨ p ⟩
                a₁ + b₂
            ≡⟨ +-comm a₁ b₂ ⟩
                b₂ + a₁
            ≡⟨ cong (λ z → z + a₁) (sym (+-rUnit b₂)) ⟩
                (b₂ + zero) + a₁
            ∎)
