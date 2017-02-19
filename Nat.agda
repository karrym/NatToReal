module Nat where

open import Data.Product
open import Data.Sum
open import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty
open import Level hiding (zero)

data ℕ : Set where
    zero : ℕ
    succ : ℕ → ℕ

open Eq.≡-Reasoning

¬_ : { ℓ : Level} → Set ℓ → Set ℓ
¬ P = P → ⊥

≡-succ : (n m : ℕ) → succ n ≡ succ m → n ≡ m
≡-succ zero .zero refl = refl
≡-succ (succ n) .(succ n) refl = refl

sn≢0 : (n : ℕ) → ¬ (succ n ≡ zero)
sn≢0 _ ()

_+_ : ℕ → ℕ → ℕ
zero + m = m
succ n + m = succ (n + m)

_*_ : ℕ → ℕ → ℕ
zero * _ = zero
succ n * m = m + (n * m)

+-rUnit : (n : ℕ) → n + zero ≡ n
+-rUnit zero = refl
+-rUnit (succ n) = begin cong succ (+-rUnit n)

+-lUnit : (n : ℕ) → zero + n ≡ n
+-lUnit _ = refl

+-assoc : (n m l : ℕ) → n + (m + l) ≡ (n + m) + l
+-assoc zero m l =
    begin
        zero + (m + l)
    ≡⟨ refl ⟩
        m + l
    ≡⟨ refl ⟩
        (zero + m) + l
    ∎
+-assoc (succ n) m l = cong succ (+-assoc n m l)

+-right : (n m : ℕ) → n + succ m ≡ succ (n + m)
+-right zero m = refl
+-right (succ n) m = cong succ (+-right n m)

+-comm : (m n : ℕ) → m + n ≡ n + m
+-comm zero n = sym (+-rUnit n)
+-comm (succ m) n = begin
        succ (m + n)
    ≡⟨ cong succ (+-comm m n) ⟩
        succ (n + m)
    ≡⟨ sym (+-right n m) ⟩
        n + succ m
    ∎

+-lCancel : (n m l : ℕ) → l + n ≡ l + m → n ≡ m
+-lCancel n m zero p = p
+-lCancel n m (succ l) p = +-lCancel n m l (≡-succ (l + n) (l + m) p)

+-rCancel : (n m l : ℕ) → n + l ≡ m + l → n ≡ m
+-rCancel n m zero p =
    begin
        n
    ≡⟨ sym (+-rUnit n) ⟩
        n + zero
    ≡⟨ p ⟩
        m + zero
    ≡⟨ +-rUnit m ⟩
        m
    ∎
+-rCancel n m (succ l) n+sl≡m+sl = +-rCancel n m l (≡-succ (n + l) (m + l)
    (begin
        succ (n + l)
    ≡⟨ sym (+-right n l) ⟩
        n + succ l
    ≡⟨ n+sl≡m+sl ⟩
        m + succ l
    ≡⟨ +-right m l ⟩
        succ (m + l)
    ∎))

*-rAbsorp : (n : ℕ) → n * zero ≡ zero
*-rAbsorp zero = refl
*-rAbsorp (succ n) = begin
        succ n * zero
    ≡⟨ refl ⟩
        zero + (n * zero)
    ≡⟨ cong (λ x → zero + x) (*-rAbsorp n) ⟩
        zero + zero
    ≡⟨ refl ⟩
        zero
    ∎

*-right : (m n : ℕ) → m * succ n ≡ (m * n) + m
*-right zero n = begin
        zero * succ n
    ≡⟨ refl ⟩
        zero
    ≡⟨ refl ⟩
        zero * n
    ≡⟨ +-rUnit (zero * n) ⟩
        (zero * n) + zero
    ∎
*-right (succ m) n = begin
        succ m * succ n
    ≡⟨ refl ⟩
        succ n + (m * succ n)
    ≡⟨ cong (λ x → succ n + x) (*-right m n) ⟩
        succ n + ((m * n) + m)
    ≡⟨ refl ⟩
        succ (n + ((m * n) + m))
    ≡⟨ cong succ (+-assoc n (m * n) m) ⟩
        succ ((n + (m * n)) + m)
    ≡⟨ sym (+-right (n + (m * n)) m) ⟩
        (succ m * n) + succ m
    ∎

+*-rDist : (m n l : ℕ) → (m + n) * l ≡ (m * l) + (n * l)
+*-rDist m n zero = begin
        (m + n) * zero
    ≡⟨ *-rAbsorp (m + n) ⟩
        zero
    ≡⟨ sym (*-rAbsorp m) ⟩
        m * zero
    ≡⟨ sym (+-rUnit (m * zero)) ⟩
        (m * zero) + zero
    ≡⟨ cong (λ x → (m * zero) + x) (sym (*-rAbsorp n)) ⟩
        (m * zero) + (n * zero)
    ∎
+*-rDist m n (succ l) = begin
        (m + n) * succ l
    ≡⟨ *-right (m + n) l ⟩
        ((m + n) * l) + (m + n)
    ≡⟨ cong (λ x → x + (m + n)) (+*-rDist m n l) ⟩
        ((m * l) + (n * l)) + (m + n)
    ≡⟨ +-assoc ((m * l) + (n * l)) m n ⟩
        (((m * l) + (n * l)) + m) + n
    ≡⟨ cong (λ x → x + n) (sym (+-assoc (m * l) (n * l) m)) ⟩
        ((m * l) + ((n * l) + m)) + n
    ≡⟨ cong (λ x → x + n) (cong (λ x → (m * l) + x) (+-comm (n * l) m)) ⟩
        ((m * l) + (m + (n * l))) + n
    ≡⟨ cong (λ x → x + n) (+-assoc (m * l) m (n * l)) ⟩
        (((m * l) + m) + (n * l)) + n
    ≡⟨ sym (+-assoc ((m * l) + m) (n * l) n) ⟩
        ((m * l) + m) + ((n * l) + n)
    ≡⟨ cong (λ x → x + ((n * l) + n)) (sym (*-right m l)) ⟩
        (m * succ l) + ((n * l) + n)
    ≡⟨ cong (λ x → (m * succ l) + x) (sym (*-right n l)) ⟩
        (m * succ l) + (n * succ l)
    ∎

*-assoc : (m n l : ℕ) → m * (n * l) ≡ (m * n) * l
*-assoc zero n l = refl
*-assoc (succ m) n l = begin
        succ m * (n * l)
    ≡⟨ refl ⟩
        (n * l) + (m * (n * l))
    ≡⟨ cong (λ x → (n * l) + x) (*-assoc m n l) ⟩
        (n * l) + ((m * n) * l)
    ≡⟨ sym (+*-rDist n (m * n) l) ⟩
        (n + (m * n)) * l
    ≡⟨ refl ⟩
        (succ m * n) * l
    ∎

*-comm : (m n : ℕ) → m * n ≡ n * m
*-comm zero n = sym (*-rAbsorp n)
*-comm (succ m) n = begin
        succ m * n
    ≡⟨ refl ⟩
        n + (m * n)
    ≡⟨ +-comm n (m * n) ⟩
        (m * n) + n
    ≡⟨ cong (λ x → x + n) (*-comm m n) ⟩
        (n * m) + n
    ≡⟨ sym (*-right n m) ⟩
        n * succ m
    ∎

_≤_ : ℕ → ℕ → Set
n ≤ m = Σ ℕ (λ l → n + l ≡ m)

≤-refl : (n : ℕ) → n ≤ n
≤-refl zero = zero , refl
≤-refl (succ n) = zero ,
    (begin
        (succ n + zero)
    ≡⟨ +-rUnit (succ n) ⟩
        (succ n)
    ∎)

0≤n : (n : ℕ) → zero ≤ n
0≤n zero = ≤-refl zero
0≤n (succ n) = succ n , refl

≤-trans : (n m l : ℕ) → n ≤ m → m ≤ l → n ≤ l
≤-trans zero m l p q = l , refl
≤-trans (succ n) m l (a , succn+a≡m) (b , m+b≡l)
    = (a + b) , (begin
        succ n + (a + b)
    ≡⟨ +-assoc (succ n) a b ⟩
        (succ n + a) + b
    ≡⟨ cong (λ x → x + b) succn+a≡m ⟩
        m + b
    ≡⟨ m+b≡l ⟩
        l
    ∎)

+-lZero : (n m : ℕ) → n + m ≡ zero → n ≡ zero
+-lZero zero m = λ _ → refl
+-lZero (succ n) m ()

≤-antisym : (n m : ℕ) → n ≤ m → m ≤ n → n ≡ m
≤-antisym n m (c , n+c≡m) (d , m+d≡n) = trans (sym n+c≡n) n+c≡m
    where
        c≡0 : c ≡ zero
        c≡0 = +-lZero c d (+-lCancel (c + d) zero n (
            begin
                n + (c + d)
            ≡⟨ +-assoc n c d ⟩
                (n + c) + d
            ≡⟨ cong (λ x → x + d) n+c≡m ⟩
                m + d
            ≡⟨ m+d≡n ⟩
                n
            ≡⟨ sym (+-rUnit n) ⟩
                n + zero
            ∎))
        n+c≡n : n + c ≡ n
        n+c≡n = begin
                n + c
            ≡⟨ cong (λ x → n + x) c≡0 ⟩
                n + zero
            ≡⟨ +-rUnit n ⟩
                n
            ∎

n+s0≡sn : (n : ℕ) → n + succ zero ≡ succ n
n+s0≡sn n = begin
        n + succ zero
    ≡⟨ +-right n zero ⟩
        succ (n + zero)
    ≡⟨ cong succ (+-rUnit n) ⟩
        succ n
    ∎

n≤sn : (n : ℕ) → n ≤ succ n
n≤sn n = succ zero , n+s0≡sn n

ℕ-ω : (n : ℕ) → n ≡ zero ⊎ Σ ℕ (λ c → n ≡ succ c)
ℕ-ω zero = inj₁ refl
ℕ-ω (succ n) = inj₂ (n , refl)

m+sn≡sm+n : (m n : ℕ) → m + succ n ≡ succ m + n
m+sn≡sm+n m zero = begin
        m + succ zero
    ≡⟨ n+s0≡sn m ⟩
        succ m
    ≡⟨ sym (+-rUnit (succ m)) ⟩
        succ m + zero
    ∎
m+sn≡sm+n m (succ n) = begin
        m + succ (succ n)
    ≡⟨ +-right m (succ n) ⟩
        succ (m + succ n)
    ≡⟨ cong succ (m+sn≡sm+n m n) ⟩
        succ (succ m + n)
    ≡⟨ sym (+-right (succ m) n) ⟩
        succ m + succ n
    ∎

sn≤m : (n m : ℕ) → n ≤ m → ¬ (n ≡ m) → succ n ≤ m
sn≤m n m (c , n+c≡m) q = lem (ℕ-ω c)
    where
        n+c≡n : c ≡ zero → n + c ≡ n
        n+c≡n p = begin
                n + c
            ≡⟨ cong (λ x → n + x) p ⟩
                n + zero
            ≡⟨ +-rUnit n ⟩
                n
            ∎
        lem : c ≡ zero ⊎ Σ ℕ (λ d → c ≡ succ d) → succ n ≤ m
        lem (inj₁ x) = ⊥-elim (q (trans (sym (n+c≡n x)) n+c≡m))
        lem (inj₂ (d , c≡sd)) = d , (begin
                succ n + d
            ≡⟨ sym (m+sn≡sm+n n d) ⟩
                n + succ d
            ≡⟨ sym (cong (λ x → n + x) c≡sd) ⟩
                n + c
            ≡⟨ n+c≡m ⟩
                m
            ∎)

≤-all : (m n : ℕ) → m ≤ n ⊎ n ≤ m
≤-all m zero = inj₂ (m , refl)
≤-all m (succ n) = lem (≤-all m n)
    where
        lem : m ≤ n ⊎ n ≤ m → m ≤ succ n ⊎ succ n ≤ m
        lem (inj₁ x) = inj₁ (≤-trans m n (succ n) x (n≤sn n))
        lem (inj₂ (zero , n+zero≡m)) = inj₁ (succ zero , (begin
                m + succ zero
            ≡⟨ +-right m zero ⟩
                succ (m + zero)
            ≡⟨ cong succ (+-rUnit m) ⟩
                succ m
            ≡⟨ cong succ (sym n+zero≡m) ⟩
                succ (n + zero)
            ≡⟨ cong succ (+-rUnit n) ⟩
                succ n
            ∎))
        lem (inj₂ (succ c , n+sc≡m)) = inj₂ (c , (begin
                succ n + c
            ≡⟨ refl ⟩
                succ (n + c)
            ≡⟨ sym (+-right n c) ⟩
                n + succ c
            ≡⟨ n+sc≡m ⟩
                m
            ∎))

+-mono : (m n l : ℕ) → m ≤ n → (m + l) ≤ (n + l)
+-mono m n zero (c , m+c≡n) = c , (begin
        (m + zero) + c
    ≡⟨ cong (λ x → x + c) (+-rUnit m) ⟩
        m + c
    ≡⟨ m+c≡n ⟩
        n
    ≡⟨ sym (+-rUnit n) ⟩
        n + zero
    ∎)
+-mono m n (succ l) (c , m+c≡n) = lem (+-mono m n l (c , m+c≡n))
    where
        lem : (m + l) ≤ (n + l) → (m + succ l) ≤ (n + succ l)
        lem (d , m+l+d≡n+l) = d , (begin
                (m + succ l) + d
            ≡⟨ cong (λ x → x + d) (+-right m l) ⟩
                succ (m + l) + d
            ≡⟨ refl ⟩
                succ ((m + l) + d)
            ≡⟨ cong succ m+l+d≡n+l ⟩
                succ (n + l)
            ≡⟨ sym (+-right n l) ⟩
                n + succ l
            ∎)

*-mono : (m n l : ℕ) → m ≤ n → (m * l) ≤ (n * l)
*-mono m n zero (c , m+c≡n) = zero , (begin
        (m * zero) + zero
    ≡⟨ +-rUnit (m * zero) ⟩
        m * zero
    ≡⟨ trans (*-rAbsorp m) (sym (*-rAbsorp n)) ⟩
        n * zero
    ∎)
*-mono m n (succ l) (c , m+c≡n) = lem (*-mono m n l (c , m+c≡n))
    where
        lem : (m * l) ≤ (n * l) → (m * succ l) ≤ (n * succ l)
        lem (d , m*l+d≡n*l) = (c * succ l) , sym (begin
                n * succ l
            ≡⟨ cong (λ x → x * succ l) (sym m+c≡n) ⟩
                (m + c) * succ l
            ≡⟨ +*-rDist m c (succ l) ⟩
                (m * succ l) + (c * succ l)
            ∎)

s≤s : (m n : ℕ) → m ≤ n → succ m ≤ succ n
s≤s zero n (c , c≡n) = n , refl
s≤s (succ m) n (c , sm+c≡n) = c , cong succ sm+c≡n

data _≲_ : ℕ → ℕ → Set where
    0≲n : {n : ℕ} → zero ≲ n
    s≲s : {n m : ℕ} → n ≲ m → succ n ≲ succ m

≤-≲ : (m n : ℕ) → m ≤ n → m ≲ n
≤-≲ zero _ _ = 0≲n
≤-≲ (succ m) zero (c , ())
≤-≲ (succ m) (succ n) (c , m+c≡n) = s≲s (≤-≲ m n (c , ≡-succ (m + c) n m+c≡n))

≲-≤ : (m n : ℕ) → m ≲ n → m ≤ n
≲-≤ .zero n 0≲n = n , refl
≲-≤ (succ m) (succ n) (s≲s p) = s≤s m n (≲-≤ m n p)
