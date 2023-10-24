{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--diff" @-}
-- {-# LANGUAGE GADTs #-}

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PackageImports #-}
module InductNatExample where

{- HLINT ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude

{-@ data N [toInt] = Z | Suc N @-}
data N = Z | Suc N deriving Eq

{-@ measure toInt @-}
{-@ toInt :: N -> {v:Int | v >= 0} @-}
toInt :: N -> Int
toInt Z = 0
toInt (Suc n) = 1 + toInt n

-- | Addition of natural numbers
{-@ reflect add @-}
add :: N -> N -> N
add Z n = n
add (Suc m) n = Suc (add m n)

-- Addition definition lemmas:
{-@ add_zero_l :: n:N -> {add Z n = n} @-}
add_zero_l Z = trivial
add_zero_l (Suc n) = add_zero_l n

{-@ add_suc_l :: m:N -> n:N -> {Suc (add m n) = add (Suc m) n} @-}
add_suc_l :: N -> N -> Proof
add_suc_l Z n = trivial
add_suc_l (Suc m) n = add_suc_l m n

-- | Addition with right zero
{-@ add_zero_r :: n:N -> {add n Z = n} @-}
add_zero_r Z     = trivial
add_zero_r (Suc n) = add_zero_r n

-- | Addition with right successor.
{-@ add_suc_r :: m:N -> n:N -> {Suc (add m n) = add m (Suc n)} @-}
add_suc_r :: N -> N -> Proof
add_suc_r Z n = trivial
add_suc_r (Suc m) n = add_suc_r m n

-- | Addition commutes
{-@ add_comm :: m:N -> n:N -> {add m n == add n m} @-}
add_comm :: N -> N -> Proof
-- add_comm n Z = add_zero_r n
add_comm Z n = add_zero_r n
add_comm (Suc m) n = add_comm m n ? add_suc_r n m

-- | Addition is associative
{-@ add_assoc :: m:N -> n:N -> o:N -> {add m (add n o) == add (add m n) o} @-}
add_assoc :: N -> N -> N -> Proof
add_assoc Z _ _ = trivial
-- add_assoc m Z o = add_zero_r m
-- add_assoc m n Z = add_zero_r n ? add_zero_r (add m n)
add_assoc (Suc m) n o = add_assoc m n o

-- | Multiplication of natural numbers
{-@ reflect mult @-}
mult :: N -> N -> N
mult Z n = Z
mult (Suc m) n = n `add` (mult m n)

-- Multiplication definition lemmas:
{-@ mult_zero_l :: n:N -> {mult Z n = Z} @-}
mult_zero_l Z     = trivial
mult_zero_l (Suc n) = mult_zero_l n

{-@ mult_suc_l :: m:N -> n:N -> {mult (Suc m) n = add n (mult m n)} @-}
mult_suc_l :: N -> N-> Proof
mult_suc_l Z _    = trivial
mult_suc_l (Suc m) n = trivial

-- | Multiplication with right zero
{-@ mult_zero_r :: n:N -> {mult n Z = Z} @-}
mult_zero_r Z     = trivial
mult_zero_r (Suc n) = mult_zero_r n

-- | Multiplication with right successor
{-@ mult_suc_r :: n:N -> m:N -> {mult n (Suc m) = add n (mult n m)} @-}
mult_suc_r :: N -> N-> Proof
mult_suc_r Z _    = trivial
mult_suc_r (Suc n) m = mult_suc_r n m
                  ? add_assoc m n (mult n m)
                  ? add_comm m n
                  ? add_assoc n m (mult n m)

{-@ reflect one @-}
one = Suc Z

{-@ reflect two @-}
two = Suc one

-- | Multiplication with right one
{-@ mult_one_r :: n:N -> {mult n one == n} @-}
mult_one_r :: N -> Proof
mult_one_r Z    = trivial
mult_one_r (Suc n) = mult_one_r n

-- | Multiplication with left one
{-@ mult_one_l :: n: N -> {mult one n == n} @-}
mult_one_l :: N -> Proof
mult_one_l n = add_zero_r n 

-- | Addition distributes over right multiplication
{-@ add_dist_rmult:: m: N -> n: N -> o: N -> {mult (add m n) o == add (mult m o) (mult n o) } @-}
add_dist_rmult :: N -> N -> N -> Proof
add_dist_rmult Z _ _ = trivial
add_dist_rmult (Suc m) n o = add_dist_rmult m n o ? add_assoc o (mult m o) (mult n o)


-- | Addition distributes over left multiplication
{-@ add_dist_lmult:: m: N -> n: N -> o: N -> {mult m (add n o) == add (mult m n) (mult m o) } @-}
add_dist_lmult :: N -> N -> N -> Proof
add_dist_lmult m Z _ = mult_zero_r m
add_dist_lmult m (Suc n) o  = mult_suc_r m (add n o) 
                            ? add_dist_lmult m n o 
                            ? add_assoc m (mult m n) (mult m o) 
                            ? mult_suc_r m n

{-@ mult_assoc :: m: N -> n: N -> o: N -> {mult (mult m n) o == mult m (mult n o)} @-}
mult_assoc :: N -> N -> N -> Proof
mult_assoc Z _ _ = trivial
-- mult_assoc m Z o = add_zero_r m
-- mult_assoc m n Z = add_zero_r n ? add_zero_r (add m n)
mult_assoc (Suc m) n o =                    mult (mult (Suc m) n) o 
                                        === (n `add` (mult m n)) `mult` o
        ? add_dist_rmult n (mult m n) o === (n `mult` o) `add` ((m `mult` n) `mult` o)
        ? mult_assoc m n o              === (n `mult` o) `add` (m `mult` (n `mult` o))
                                        === (Suc m) `mult` (mult n o)           *** QED

{-@ add_mono_r :: m: N -> n: N -> {geqN (add m n) m && (geN n Z => geN (add m n) m)}  @-}
add_mono_r :: N -> N -> Proof
add_mono_r Z n = trivial
add_mono_r (Suc m) n = add_suc_l m n ? add_mono_r m n

{-@ add_mono_l :: m: N -> n: N -> {geqN (add m n) n && (geN m Z => geN (add m n) n)}  @-}
add_mono_l :: N -> N -> Proof
add_mono_l m n = add_mono_r n m ? add_comm n m

{-@ mult_zero :: m: N -> n: N -> {m != Z && n != Z => geqN (mult m n) n} @-}
mult_zero :: N -> N -> Proof
mult_zero Z _ = trivial
mult_zero (Suc m) n = ((Suc m) `mult` n ? mult_suc_l m n === n `add` (m `mult` n) ? add_comm n (mult m n) === (m `mult` n) `add` n *** QED) ? ge_zero n ? add_mono_l (m `mult` n) n ? ge_geq ((m `mult` n) `add` n) n

-- | Equality of natural numbers
{-@ reflect eqN @-}
{-@ eqN :: m:N -> n:N -> {r:Bool | r = (m == n) }@-}
eqN Z Z = True
eqN (Suc m) (Suc n) = eqN m n
eqN _ _ = False

{-@ eq_equal :: m:N -> n:N -> {(eqN m n) <=> (m == n)} @-}
eq_equal :: N -> N -> Proof
eq_equal Z Z = trivial
eq_equal (Suc m) (Suc n) = eq_equal m n
eq_equal _ _ = trivial

{-@ eq_sym :: m: N -> n: N -> {eqN m n <=> eqN n m} @-}
eq_sym :: N -> N -> Proof
eq_sym m n = eq_equal m n ? eq_equal n m

-- | Greater than or equals for natural numbers
{-@ reflect geqN @-}
{-@ geqN :: m: N -> n:N -> {p: Bool | p = (toInt m >= toInt n)} @-}
geqN :: N -> N -> Bool
geqN _ Z = True
geqN Z (Suc _) = False
geqN (Suc m) (Suc n) = geqN m n

{-@ eq_geq:: m: N -> n: N -> {eqN m n ==> geqN m n} @-}
eq_geq :: N -> N -> Proof
eq_geq (Suc m) (Suc n) = eq_geq m n
eq_geq _ Z = trivial
eq_geq Z (Suc _) = trivial

{-@ reflect leqN @-}
{-@ leqN :: m: N -> n: N -> {p:Bool | p = (toInt m <= toInt n) } @-}
leqN m n = geqN n m

-- | geqN is a reflexive relation
{-@ geqN_refl :: n:N -> {geqN n n} @-}
geqN_refl :: N -> Proof
geqN_refl Z = trivial
geqN_refl (Suc n) = geqN_refl n

-- | geqN is transitive
{-@ geqN_trans :: m:N -> n:N -> o:N -> {geqN m n && geqN n o ==> geqN m o} @-}
geqN_trans :: N -> N -> N -> Proof
geqN_trans _ _ Z = trivial
geqN_trans _ Z _ = trivial
geqN_trans Z _ _ = trivial
geqN_trans (Suc m) (Suc n) (Suc o) = geqN_trans m n o


-- | Strictly greater than for natural numbers
{-@ reflect geN @-}
{-@ geN :: m: N -> n: N -> {p:Bool | (p = (toInt m > toInt n)) && (p ==> geqN m n)} @-}
geN :: N -> N -> Bool
geN Z _ = False
geN (Suc _) Z = True
geN (Suc m) (Suc n) = geN m n

{-@ ge_measure :: m: N -> n: N -> {geN m n <=> toInt m > toInt n} @-}
ge_measure :: N -> N -> Proof
ge_measure Z _ = trivial
ge_measure (Suc _) Z = trivial
ge_measure (Suc m) (Suc n) = ge_measure m n

{-@ ge_zero :: n : N -> {geqN n Z && n != Z => geN n Z} @-}
ge_zero Z = trivial
ge_zero (Suc n) = ge_zero n ? ge_geq_suc n Z

{-@ ge_geq_suc :: m: N -> n: N -> { geN m n <=> geqN m (Suc n)} @-}
ge_geq_suc :: N -> N -> Proof
ge_geq_suc Z _ = trivial
ge_geq_suc (Suc m) Z = trivial
ge_geq_suc (Suc m) (Suc n) = ge_geq_suc m n

{-@ eq_suc_ge :: m: N -> n: N -> {eqN m n ==> geN (Suc m) n}@-}
eq_suc_ge :: N -> N -> Proof
eq_suc_ge (Suc m) (Suc n) = eq_suc_ge m n
eq_suc_ge Z Z = trivial
eq_suc_ge Z (Suc n) = trivial
eq_suc_ge (Suc m) Z = trivial

{-@ reflect leN @-}
{-@ leN :: m: N -> n: N -> {p:Bool | p = (toInt m < toInt n) } @-}
leN m n = geN n m

{-@ le_geq :: m : N -> n: N -> {geqN m n = not (leN m n)} @-}
le_geq _ Z = trivial
le_geq Z (Suc n) = trivial
le_geq (Suc m) (Suc n) = le_geq m n

{-@ ge_geq :: m : N -> n: N -> {geN m n ==> geqN m n} @-}
ge_geq :: N -> N -> Proof
ge_geq (Suc m) (Suc n) = ge_geq m n
ge_geq Z Z = trivial
ge_geq Z (Suc n) = trivial
ge_geq (Suc m) Z = trivial

-- | geN is an anti-commutative relation
{-@ geN_anti_comm :: m: N -> n:N -> {geN m n ==> not geN n m} @-}
geN_anti_comm :: N -> N -> Proof
geN_anti_comm Z Z = trivial
geN_anti_comm Z (Suc n) = trivial
geN_anti_comm (Suc m) Z = trivial
geN_anti_comm (Suc m) (Suc n) = geN_anti_comm m n

{-@ geN_irreflexive :: m: N -> n:N -> {geN m n ==> not eqN m n} @-}
geN_irreflexive :: N -> N -> Proof
geN_irreflexive (Suc m) (Suc n) = geN_irreflexive m n
geN_irreflexive _ _ = trivial

-- | geN is transitive
{-@ geN_trans :: m:N -> n:N -> o:N -> {geN m n && geN n o ==> geN m o} @-}
geN_trans :: N -> N -> N -> Proof
geN_trans _ Z _ = trivial
geN_trans Z _ _ = trivial
geN_trans (Suc m) _ Z = trivial
geN_trans (Suc m) (Suc n) (Suc o) = geN_trans m n o

-- | geN transitive with eq
{-@ geN_eq_trans :: m:N -> n:N -> o:N -> {geN m n && eqN n o ==> geN m o} @-}
geN_eq_trans :: N -> N -> N -> Proof
geN_eq_trans _ Z Z = trivial
geN_eq_trans _ Z (Suc _) = trivial
geN_eq_trans Z _ _ = trivial
geN_eq_trans (Suc m) _ Z = trivial
geN_eq_trans (Suc m) (Suc n) (Suc o) = geN_eq_trans m n o

-- useful lemma
{-@ geqN_suc_l:: m: N -> {n: N | geqN m n} -> {geqN (Suc m) n} @-}
geqN_suc_l :: N -> N -> Proof
geqN_suc_l (Suc m) (Suc n) = geqN_suc_l m n
geqN_suc_l (Suc m) Z = trivial
geqN_suc_l Z Z = trivial
geqN_suc_l Z (Suc n) = trivial

{-@ geq_ge_suc:: m: N -> {n: N | geqN m n} -> {geN (Suc m) n} @-}
geq_ge_suc :: N -> N -> Proof
geq_ge_suc (Suc m) (Suc n) = geq_ge_suc m n
geq_ge_suc (Suc m) Z = trivial
geq_ge_suc Z Z = trivial
geq_ge_suc Z (Suc n) = trivial


-- useful lemma
{-@ geN_suc_l:: m: N -> {n: N | geN m n} -> {geN (Suc m) n} @-}
geN_suc_l :: N -> N -> Proof
geN_suc_l (Suc m) (Suc n) = geN_suc_l m n
geN_suc_l (Suc m) Z = trivial
geN_suc_l Z Z = trivial
geN_suc_l Z (Suc n) = trivial

-- | geqN = geN union eqN
{-@ geqN_geN_eqN:: m: N -> n: N -> { geqN m n <=> geN m n || eqN m n} @-}
geqN_geN_eqN:: N -> N -> Proof
geqN_geN_eqN Z Z = trivial
geqN_geN_eqN (Suc m) Z = trivial
geqN_geN_eqN Z (Suc n) = trivial
geqN_geN_eqN (Suc m) (Suc n) = geqN_geN_eqN m n

{-@ geqN_not_le:: n : N -> m: N -> {geqN m n <=> not (leN m n)} @-}
geqN_not_le:: N -> N -> Proof
geqN_not_le Z Z = trivial
geqN_not_le (Suc m) Z = trivial
geqN_not_le Z (Suc n) = trivial
geqN_not_le (Suc m) (Suc n) = geqN_not_le m n

{-@ ge_eq_le_exhaustive :: m: N -> n: N -> {geN m n || eqN m n || leN m n} @-}
ge_eq_le_exhaustive :: N -> N -> Proof
ge_eq_le_exhaustive Z Z = trivial
ge_eq_le_exhaustive (Suc m) Z = trivial
ge_eq_le_exhaustive Z (Suc n) = trivial
ge_eq_le_exhaustive (Suc m) (Suc n) = ge_eq_le_exhaustive m n

-- | subtraction of natural numbers, only works if subtracting from a number greater or equal to the number we subtract from it
{-@ reflect subt @-}
{-@ subt :: m:N -> {n:N | geqN m n} -> {o:N | n != Z = toInt o < toInt m} @-}
subt Z Z = Z
subt (Suc m) Z = Suc m
subt (Suc m) (Suc n) = subt m n

-- | subtracting a number from itself yields Z
{-@ subt_self :: m: N -> n: N -> {eqN m n ==> subt m n = Z} @-}
subt_self (Suc m) (Suc n) = subt_self m n
subt_self _ _ = trivial

-- | adding and then subtracting a number is identity
{-@ add_subt :: m:N -> n:N -> {subt (add m n) n = m }@-}
add_subt :: N -> N -> Proof
add_subt Z Z = trivial
add_subt (Suc m) Z = add_zero_r m
add_subt m (Suc n) = add_suc_r m n ? add_subt m n

{-@ subt_suc_l :: m: N -> {n:N | geqN m n} -> {subt (Suc m) n == Suc (subt m n)} @-}
subt_suc_l :: N -> N-> Proof
subt_suc_l Z Z = trivial
subt_suc_l (Suc m) Z = trivial
subt_suc_l (Suc m) (Suc n) = subt_suc_l m n

-- required lemma for next proof
{-@ geqN_suc:: n: N -> {geqN (Suc n) n}@-}
geqN_suc :: N -> Proof
geqN_suc Z = trivial
geqN_suc (Suc n) = geqN_suc n

-- | subtraction yields a smaller number
{-@ subt_leqN :: m: N -> {n: N | geqN m n} -> {geqN m (subt m n)} @-}
subt_leqN Z Z = trivial
subt_leqN (Suc m) Z = geqN_refl m
subt_leqN (Suc m) (Suc n)   = subt_leqN m n                     -- m >= m - n
                            ? geqN_suc m                        -- Suc m >= m
                            ? geqN_trans (Suc m) m (subt m n)   -- Suc m >= m - n


{-@ subt_leN :: m: N -> {n: N | geqN m n} -> {n != Z => geN m (subt m n)} @-}
subt_leN Z Z = trivial
subt_leN (Suc m) Z = geqN_refl m
subt_leN (Suc m) (Suc n)    = ((Suc m) `subt` (Suc n) === m `subt` n *** QED)
                            ? subt_leqN m n                      -- m >= m - n
                            ? geq_ge_suc m (m `subt` n)           -- m >= (m - n) => S m > m - n 
                            ? eq_equal (m `subt` n) ((Suc m) `subt` (Suc n))
                            ? geN_eq_trans (Suc m) (m `subt` n) ((Suc m) `subt` (Suc n))


{-@ ge_subt :: m: N -> {n:N | geN m n} -> {geN (subt m n) n ==> geN m n} @-}
ge_subt (Suc m) Z = trivial
ge_subt (Suc m) (Suc n) = ge_subt m n ? geqN_geN_eqN m n ? geqN_suc_l m n

{-@ notZ :: {n:N | n != Z} -> {geN (Suc n) one} @-}
notZ :: N -> Proof
notZ Z = trivial
notZ (Suc n) = trivial

-- {-@ reflect impossibleValue @-}
{-@ impossibleValue :: {s:String | False} -> a @-}
impossibleValue :: String -> a
impossibleValue s = Prelude.error s

-- | modulo operation for natural numbers
{-@ reflect modN @-}
{-@ modN :: m:N -> {n:N | n != Z} -> {o:N | leN o n && o != Z ==> toInt o < toInt n && toInt o <= toInt m} @-}
modN ::N -> N -> N
modN Z n = Z
modN m n
            | m `geN` n = modN (subt m n) n
            | m `eqN` n = Z
            | m `leN` n = m
            -- it is easy to prove this case is impossible, but without it LH complains about a missing case
            -- we cannot use impossibleValue here as we need to be able to reflect on this function
            | otherwise = Z -- impossibleValue "ge, eq and le are exhaustive"

-- | Definition lemmas:
-- | Lemma: m < n => m mod n = m
{-@ ineffective_mod :: m:N -> {n:N | n != Z} -> {leN m n ==> modN m n = m} @-}
ineffective_mod :: N -> N -> Proof
ineffective_mod m n 
            | m `geN` n = geN_anti_comm n m
            | m `eqN` n = geN_irreflexive n m
            | m `leN` n = modN m n === m *** QED
            | otherwise = ge_eq_le_exhaustive m n

{-@ equal_mod :: m:N -> {n:N | n != Z} -> {eqN m n ==> modN m n = Z} @-}
equal_mod :: N -> N -> Proof
equal_mod m n 
            | m `geN` n = geN_irreflexive m n
            | m `eqN` n = modN m n === Z *** QED
            | m `leN` n = geN_irreflexive n m
            | otherwise = ge_eq_le_exhaustive m n

-- | Lemma: m >= n => m mod n == m - n mod n
{-@ subt_mod :: m: N -> {n: N | geqN m n} -> {modN (subt m n) n == modN m n} @-}
subt_mod :: N -> N -> Proof
subt_mod Z _ = trivial
subt_mod m n 
            | m `geN` n = trivial
            | m `eqN` n = subt_self m n
            | m `leN` n = le_geq m n
            | otherwise = geqN_geN_eqN m n


{-@ modN_post :: m:N -> {n:N | n != Z} -> {leN (modN m n) n} @-}
modN_post :: N -> N -> Proof
modN_post m Z = trivial
modN_post m (Suc n) 
            | m `geN` (Suc n) = modN_post (subt m (Suc n)) (Suc n)
            | m `eqN` (Suc n) = trivial
            | m `leN` (Suc n) = m `modN` (Suc n) === m *** QED
            | otherwise = trivial

{-@ one_mod :: n: N -> {geN n one ==> modN one n == one} @-}
one_mod :: N -> Proof
one_mod n 
            | one `geN` n = geN_anti_comm one n
            | one `eqN` n = geN_irreflexive one n
            | one `leN` n = trivial
            | otherwise = geqN_geN_eqN one n

{-@ m_le_n_mod_suc :: m: N -> {n:N | n != Z} -> {geN n (Suc m) => modN (Suc m) n == Suc m} @-}
m_le_n_mod_suc :: N -> N -> Proof
m_le_n_mod_suc m n = ineffective_mod (Suc m) n

-- | Lemma:     m: N -> {n: N | n != Z} -> {n > S (m mod n) => S m mod n == S (m mod n)}
{-@ modN_suc_1:: m: N -> {n:N | n != Z} -> {geN n (Suc (modN m n)) ==> modN (Suc m) n == Suc (modN m n)} @-}
modN_suc_1 :: N -> N -> Proof
-- modN_suc_1 Z one = notZ one ? one_mod_n one
-- modN_suc_1 Z (Suc n) = notZ n ? one_mod_n (Suc n)
modN_suc_1 m n 
            | m `geN` n = modN_suc_1 (subt m n) n           -- n > S (m - n mod n) => S (m - n) mod n == S (m - n mod n)
-- Need:        n > S (m mod n) => (S m) mod n == S (m mod n)
                        ? subt_mod m n                      -- m - n mod n == m mod n
-- Have:        n > S (m mod n) => S (m - n) mod n == S (m mod n)
-- Still need:  n > S (m mod n) => (S m) mod n == S (m - n) mod n
                        ? ge_geq_suc m n                    -- m >= S n
                        ? geqN_suc_l m (Suc n)              -- S m >= S n  or equivalently m >= n
                        ? geqN_suc_l m n                    -- S m >= n
                        ? subt_mod (Suc m) n                -- S m mod n == (S m) - n mod n
                        ? subt_suc_l m n                    -- (S m) - n mod n == S (m - n) mod n

            | m `eqN` n = eq_suc_ge m n                     -- S m > n
                        ? geqN_geN_eqN m n                  -- m >= n <==> m > n || m == n          this yields m >= n
                        ? geqN_suc_l m n                    -- m >= n => S m >= n
-- Need:        n > 1 => S m mod n == 1
                        ? subt_mod (Suc m) n                -- S m mod n == (S m) - n mod n
                        ? subt_suc_l m n                    -- (S m) - n mod n == S (m - n) mod n
                        ? subt_self m n                     -- m - n = Z
-- Still need:  n > 1 => one mod n == 1
                        ? one_mod n

            | m `leN` n = ineffective_mod m n               -- m mod n == m
                        ? m_le_n_mod_suc m n
-- Need:        n > S m => (S m) mod n == S m

            | otherwise = ge_eq_le_exhaustive m n

-- Lemmas required to prove modN_suc_2:

-- n != Z &&  => S m mod n == Z
{-@ modN_suc_2_ge_concl:: m: N -> {n:N | n != Z && eqN n (Suc (modN m n)) && geN m n} -> {modN (Suc m) n == modN (Suc (subt m n)) n} @-}
modN_suc_2_ge_concl :: N -> N -> Proof
modN_suc_2_ge_concl m n = (Suc m) `modN` n ? ge_geq_suc m n ? geqN_suc_l m (Suc n) ? geqN_suc_l m n ? subt_mod (Suc m) n === (Suc m) `subt` n `modN` n ? subt_suc_l m n === Suc (m `subt` n) `modN` n *** QED

-- n  != Z && n == S (m mod n) && m == n => 1 == n && 1 == m
{-@ modN_suc_2_eq_ass:: m: N -> {n:N | n != Z && eqN n (Suc (modN m n)) && eqN m n} -> {one == n && one == m} @-}
modN_suc_2_eq_ass :: N -> N -> Proof
modN_suc_2_eq_ass m n = m ? eq_equal m n === n ? eq_equal n (Suc (modN m n)) === (Suc (modN m n)) ? equal_mod m n === (Suc Z) === one *** QED

-- n != Z && 1 == n && 1 == m => S m mod n == Z
{-@ modN_suc_2_eq_concl:: m: N -> {n:N | n != Z && one == n && one == m} -> {modN (Suc m) n == Z} @-}
modN_suc_2_eq_concl :: N -> N -> Proof
modN_suc_2_eq_concl m n = (Suc m) `modN` n === two `modN` n === two `modN` one === one `modN` one === Z `modN` one === Z *** QED

-- n != Z && n = S (m mod n) && m < n => n == S m
{-@ modN_suc_2_le_ass:: m: N -> {n:N | n != Z && eqN n (Suc (modN m n)) && leN m n} -> {n == Suc m} @-}
modN_suc_2_le_ass :: N -> N -> Proof
modN_suc_2_le_ass m n = n ? eq_equal n (Suc (modN m n)) === (Suc (modN m n)) ? ineffective_mod m n === Suc m *** QED

-- n != Z && n = S m => S m mod n == Z
{-@ modN_suc_2_le_concl:: m: N -> {n:N | n != Z && n == Suc m} -> {modN (Suc m) n == Z} @-}
modN_suc_2_le_concl :: N -> N -> Proof
modN_suc_2_le_concl m n = (Suc m) `modN` n === n `modN` n ? geqN_refl n ? subt_mod n n === (n `subt` n) `modN` n ? subt_self n n ? eq_equal n n === Z `modN` n === Z *** QED

{-@ modN_suc_2:: m: N -> {n:N | n != Z && eqN n (Suc (modN m n))} -> {modN (Suc m) n = Z} @-}
modN_suc_2 :: N -> N -> Proof
modN_suc_2 m n 
            | m `geN` n = modN_suc_2 (subt m n) n           -- n == S (m - n mod n) => S (m - n) mod n == Z
                        ? subt_mod m n                      -- m - n mod n == m mod n
                        ? modN_suc_2_ge_concl m n
            | m `eqN` n = modN_suc_2_eq_ass m n ? modN_suc_2_eq_concl m n
            | m `leN` n = modN_suc_2_le_ass m n ? modN_suc_2_le_concl m n
            | otherwise = ge_eq_le_exhaustive m n

-- | division (without remainder) of natural numbers
{-@ reflect divN @-}
{-@ divN :: m:N -> {n:N | n != Z} -> N @-}
divN :: N -> N -> N
divN m n
            -- the superfluous condition m `geqN` n is required as typechecker cannot figure out m `geN` n => m `geqN` n which is precondition of subt
            | m `geN` n && m `geqN` n = Suc (divN (subt m n) n)
            | m `eqN` n = one
            | otherwise = Z

-- | Lemma: m >= n => m / n == S ((m - n) / n)
{-@ divN_subt :: m: N -> {n: N | n != Z && geqN m n} -> {Suc (divN (subt m n) n) == divN m n} @-}
divN_subt :: N -> N -> Proof
divN_subt m n 
            | m `geN` n && m `geqN` n = trivial
            | m `eqN` n = subt_self m n
            | m `leN` n = le_geq m n
            | otherwise = geqN_geN_eqN m n

{-@ divN_zero :: m: N -> {n: N | n != Z && leN m n} -> {divN m n == Z} @-}
divN_zero :: N -> N -> Proof
divN_zero m n = m `divN` n ? geN_anti_comm m n ? geN_irreflexive n m ? eq_sym m n === Z *** QED

{-@ divN_one :: m: N -> {n: N | n != Z && eqN m n} -> {divN m n == one} @-}
divN_one :: N -> N -> Proof
divN_one m n 
            | m `geN` n && m `geqN` n = geN_irreflexive m n
            | m `eqN` n = m `divN` n === one *** QED
            | otherwise = trivial    

{-@ div_mult :: m: N -> {n: N | n != Z} -> {divN (mult m n) n == m} @-}
div_mult Z (Suc n) = mult_zero_l (Suc n) ? divN_zero Z (Suc n)
div_mult (Suc m) n =                                        ((Suc m) `mult` n) `divN` n
                                                        === (n `add` (m `mult` n)) `divN` n
        ? mult_zero m n ? add_mono_r n (m `mult` n) 
        ? add_mono_r (n `add` (m `mult` n)) n ? divN_subt (n `add` (m `mult` n)) n 
                                                        === Suc (((n `add` (m `mult` n)) `subt` n) `divN` n)
        ? add_comm n (m `mult` n)                       === Suc ((((m `mult` n) `add` n) `subt` n) `divN` n)
        ? add_subt (m `mult` n) n                       === Suc ((m `mult` n) `divN` n)
        ? div_mult m n                                  === Suc m                                   *** QED


-- n > S (m mod n) => (S (m - n) / n == (m - n) / n) && m > n => S (m - n) / n == (m - n) / n => S m / n = m / n
{-@ divN_suc_1_ge_concl:: m: N -> {n:N | n != Z && geN n (Suc (modN m n)) && divN (Suc (subt m n)) n = divN (subt m n) n && geqN m n} -> {divN (Suc (subt m n)) n = divN (subt m n) n => divN (Suc m) n = divN m n} @-}
divN_suc_1_ge_concl :: N -> N -> Proof
divN_suc_1_ge_concl m n =                           m `divN` n
                        ? divN_subt m n          === Suc ((m `subt` n) `divN` n)     
                                                === Suc ((Suc (m `subt` n)) `divN` n)   
    ? geqN_suc_l m n    ? subt_suc_l m n        === Suc (((Suc m) `subt` n) `divN` n)
    ? geqN_suc_l m n    ? divN_subt (Suc m) n    === (Suc m) `divN` n    *** QED

-- n  != Z && n > S (m mod n) && m == n => n >  S (m - n mod n)
{-@ divN_suc_1_eq_ass:: m: N -> {n:N | n != Z && geN n (Suc (modN m n)) && eqN m n} -> {geN n (Suc (modN (subt m n) n))} @-}
divN_suc_1_eq_ass :: N -> N -> Proof
divN_suc_1_eq_ass m n = Suc (m `modN` n) ? eq_geq m n   ? subt_mod m n  === Suc ((m `subt` n) `modN` n)
                                                        ? subt_self m n === Suc (Z `modN` n)
                                                                        === one *** QED

-- n > S (m mod n) => (S (m - n) / n == (m - n) / n) && m == n => S m / n = m / n
{-@ divN_suc_1_eq_concl:: m: N -> {n:N | n != Z && geN n (Suc (modN m n)) && divN (Suc (subt m n)) n = divN (subt m n) n && eqN m n} -> {divN (Suc (subt m n)) n = divN (subt m n) n => divN (Suc m) n = divN m n} @-}
divN_suc_1_eq_concl :: N -> N -> Proof
divN_suc_1_eq_concl m n =                           m `divN` n
    ? eq_geq m n        ? divN_subt m n          === Suc ((m `subt` n) `divN` n)
                                                === Suc ((Suc (m `subt` n)) `divN` n)   
    ? geqN_suc_l m n    ? subt_suc_l m n        === Suc (((Suc m) `subt` n) `divN` n)
    ? geqN_suc_l m n    ? divN_subt (Suc m) n    === (Suc m) `divN` n    *** QED


{-@ divN_suc_1_suc_eq_ass:: m: N -> {n:N | n != Z && geN n (Suc (modN m n)) && eqN n (Suc m)} -> {leN m n} @-}
divN_suc_1_suc_eq_ass :: N -> N -> Proof
divN_suc_1_suc_eq_ass m n = eq_geq n (Suc m) ? ge_geq_suc n m

{-@ divN_suc_1_suc_eq_concl:: m: N -> {n:N | n != Z && geN n (Suc (modN m n)) && eqN n (Suc m) && leN m n} -> {False} @-}
divN_suc_1_suc_eq_concl :: N -> N -> Proof
divN_suc_1_suc_eq_concl m n = Suc (modN m n) ? ineffective_mod m n === Suc m *** QED ? geN_irreflexive n (Suc m)

{-@ divN_suc_1_suc_le_ass:: m: N -> {n:N | n != Z && geN n (Suc (modN m n)) && leN (Suc m) n && leN m n} -> {divN m n == Z && divN (Suc m) n == Z} @-}
divN_suc_1_suc_le_ass :: N -> N -> Proof
divN_suc_1_suc_le_ass m n = divN_zero m n ? divN_zero (Suc m) n

-- n > S (m mod n) => S m / n == m / n
{-@ divN_suc_1:: m: N -> {n:N | n != Z && geN n (Suc (modN m n))} -> {divN (Suc m) n == divN m n} @-}
divN_suc_1 :: N -> N -> Proof
divN_suc_1 m n 
            | m `geN` n  = ge_geq m n ? divN_suc_1 (subt m n) n ? subt_mod m n ? divN_suc_1_ge_concl m n
            | m `eqN` n = eq_sym m n ? eq_geq n m ? divN_suc_1_eq_ass m n ? divN_suc_1 (subt m n) n ? divN_suc_1_eq_concl m n
            | m `leN` n && n `leN` Suc m = geN_suc_l n (Suc m) ? geN_anti_comm n m
            | m `leN` n && n `eqN` Suc m = divN_suc_1_suc_eq_ass m n ? divN_suc_1_suc_eq_concl m n
            | m `leN` n && n `geN` Suc m = divN_suc_1_suc_le_ass m n
            | otherwise  = ge_eq_le_exhaustive m n ? ge_eq_le_exhaustive n (Suc m)

{-@ divN_suc_2:: m: N -> {n:N | n != Z && eqN n (Suc (modN m n))} -> {divN (Suc m) n = Suc (divN m n)} @-}
divN_suc_2 :: N -> N -> Proof
divN_suc_2 m n 
            | m `geN` n  = ge_geq m n ? geN_suc_l m n ? ge_geq (Suc m) n ? divN_suc_2 (subt m n) n ? subt_mod m n ? divN_subt m n ? divN_subt (Suc m) n ? subt_suc_l m n
            | m `eqN` n =                                                       (Suc m) `divN` n 
                ? eq_suc_ge m n ? ge_geq (Suc m) n  ? divN_subt (Suc m) n   === Suc (((Suc m) `subt` n) `divN` n) 
                                ? eq_geq m n        ? subt_suc_l m n        === Suc ((Suc (m `subt` n)) `divN` n)
                                ? subt_self m n                             === Suc ((Suc Z) `divN` n)
                                ? modN_suc_2_eq_ass m n ? divN_one one n    === Suc (one `divN` n)
                                ? eq_equal m one                            === Suc (m `divN` n)    *** QED
            | m `leN` n && n `leN` Suc m = geN_suc_l n (Suc m)  ? geN_anti_comm n m
            | m `leN` n && n `eqN` Suc m = (Suc m) `divN` n 
                                ? eq_sym n (Suc m)  ? divN_one (Suc m) n    === one
                                                                            === Suc Z 
                                ? divN_zero m n                             === Suc (m `divN` n)    *** QED
            | m `leN` n && n `geN` Suc m = ineffective_mod m n ? geN_irreflexive (Suc m) n
            | otherwise  = ge_eq_le_exhaustive m n ? ge_eq_le_exhaustive n (Suc m)

{-@ divMod_cases :: m:N -> {n:N | n != Z} -> {leN n (Suc (modN m n)) => False} @-}
divMod_cases :: N -> N -> Proof
divMod_cases m n = modN_post m n ? ge_geq_suc n (m `modN` n) ? le_geq n (Suc (m `modN` n))

-- | division with remainder is correct
{-@ divModN :: m:N -> {n:N | n != Z} -> {add (modN m n) (mult (divN m n) n) == m} @-}
divModN :: N -> N -> Proof
divModN Z Z = trivial
divModN Z (Suc n) = trivial
divModN (Suc m) n
                   | geN n (Suc (m `modN` n)) =             ((Suc m) `modN` n) `add` (((Suc m) `divN` n) `mult` n)
                                ? modN_suc_1 m n        === (Suc (m `modN` n)) `add` (((Suc m) `divN` n) `mult` n)
                                ? divN_suc_1 m n        === (Suc (m `modN` n)) `add` ((m `divN` n) `mult` n)
                                                        === Suc (m `modN` n) `add` ((m `divN` n) `mult` n)
                                ? divModN m n           === Suc (m)                                         *** QED
                   | eqN n (Suc (m `modN` n)) =             ((Suc m) `modN` n) `add` (((Suc m) `divN` n) `mult` n)
                                ? modN_suc_2 m n        === Z `add` (((Suc m) `divN` n) `mult` n)
                                ? divN_suc_2 m n        === Z `add` ((Suc (m `divN` n)) `mult` n)
                                                        === (Suc (m `divN` n)) `mult` n
                            ? mult_suc_l (m `divN` n) n === n `add` ((m `divN` n) `mult` n)
                        ? eq_equal n (Suc (m `modN` n)) === (Suc (m `modN` n)) `add` ((m `divN` n) `mult` n)
                                                        === Suc ((m `modN` n) `add` ((m `divN` n) `mult` n))
                                ? divModN m n           === Suc (m)                                         *** QED
                   | leN n (Suc (m `modN` n)) = divMod_cases m n
                   | otherwise = ge_eq_le_exhaustive n (Suc (m `modN` n))

{-@ reflect divides @-}
{-@ divides :: {m:N | m != Z} -> n:N -> o: Bool @-}
divides :: N -> N -> Bool
divides m n = eqN (n `modN` m) Z

{-@ divides_def :: {m:N | m != Z} -> n:N -> {divides m n <=> ((modN n m) == Z)} @-}
divides_def :: N -> N -> Proof
divides_def m n = divides m n === eqN (n `modN` m) Z ? eq_equal (n `modN` m) Z  === (n `modN` m) == Z   *** QED

{-@ divides_exists :: {m:N | m != Z} -> {n:N | divides m n} -> {mult (divN n m) m == n} @-}
divides_exists :: N -> N -> Proof
divides_exists m n =                    n
                    ? divModN n m   === (n `modN` m) `add` ((n `divN` m) `mult` m)
                ? divides_def m n   === Z `add` ((n `divN` m) `mult` m)
                                    === (n `divN` m) `mult` m           *** QED

{-@ exists_divides_lem :: {m:N | m != Z} -> {n:N | mult (divN n m) m == n} -> {add (modN n m) (mult (divN n m) m) == mult (divN n m) m} @-}
exists_divides_lem :: N -> N -> Proof
exists_divides_lem m n =            (n `modN` m) `add` ((n `divN` m) `mult` m)
                ? divModN n m   === n
                                === ((n `divN` m) `mult` m)       *** QED

{-@ exists_divides :: {m:N | m != Z} -> {n:N | mult (divN n m) m == n} -> {divides m n} @-}
exists_divides :: N -> N -> Proof
exists_divides m n =                                        (Z
        ? exists_divides_lem m n    ? eq_equal ((n `modN` m) `add` ((n `divN` m) `mult` m)) ((n `divN` m) `mult` m)
        ? eq_geq ((n `modN` m) `add` ((n `divN` m) `mult` m)) ((n `divN` m) `mult` m)
        ? subt_self ((n `modN` m) `add` ((n `divN` m) `mult` m)) ((n `divN` m) `mult` m)
                                                        === ((n `modN` m) `add` ((n `divN` m) `mult` m)) `subt` ((n `divN` m) `mult` m)
        ? add_subt (n `modN` m) ((n `divN` m) `mult` m) === n `modN` m              *** QED) ? divides_def m n

{-@ divides_def_exists :: {m:N | m != Z} -> n:N -> {divides m n <=> mult (divN n m) m == n} @-}
divides_def_exists :: N -> N -> Proof
divides_def_exists m n 
                | (n `divN` m) `mult` m == n = exists_divides m n
                | divides m n = divides_exists m n
                | otherwise = trivial

{-@ divides_self :: {n:N | n != Z} -> {divides n n} @-}
divides_self :: N -> Proof
divides_self n = divides_def n n ? ((n `modN` n) ? geqN_refl n  ? subt_mod n n  === (n `subt` n) `modN` n
                                                 ? eq_equal n n ? subt_self n n === Z `modN` n
                                                                                === Z           *** QED)

{-@ divides_zero :: {n:N | n != Z} -> {divides n Z} @-}
divides_zero :: N -> Proof
divides_zero n = (Z `modN` n     === Z   *** QED) ? divides_def n Z

{-@ divides_eqN :: {m:N | m != Z} -> {n:N | eqN m n} -> {divides m n} @-}
divides_eqN :: N -> N -> Proof
divides_eqN m n = eq_equal m n ? divides_self m

{-@ divides_mod_eqs :: m:N -> {n:N | n != Z} -> {o: N | o != Z && mult (divN n o) o == n && mult (divN (modN m n) o) o == (modN m n)} -> {mult (add (mult (divN m n) (divN n o)) (divN (modN m n) o)) o == m} @-}
divides_mod_eqs :: N -> N -> N -> Proof
divides_mod_eqs m n o = mult (add (mult (divN m n) (divN n o)) (divN (modN m n) o)) o ==! m *** QED


{-@ divides_mod_ass :: m:N -> {n:N | n != Z} -> {o: N | o != Z && mult (divN n o) o == n && mult (divN (modN m n) o) o == (modN m n)} -> {add (mult (divN m n) (divN n o)) (divN (modN m n) o) == divN m o} @-}
divides_mod_ass :: N -> N -> N -> Proof
divides_mod_ass m n o =                                                     m `divN` o
                                                ? divides_mod_eqs m n o === ((add (mult (divN m n) (divN n o)) (divN (modN m n) o)) `mult` o) `divN` o
    ? div_mult (add (mult (divN m n) (divN n o)) (divN (modN m n) o)) o === add (mult (divN m n) (divN n o)) (divN (modN m n) o)                *** QED

{-@ divides_mod_concl :: m:N -> {n:N | n != Z} -> {o: N | o != Z && mult (divN n o) o == n && mult (divN (modN m n) o) o == (modN m n)} -> {mult (divN m o) o == m} @-}
divides_mod_concl :: N -> N -> N -> Proof
divides_mod_concl m n o =               (m `divN` o) `mult` o
        ? divides_mod_ass m n o     === (((m `divN` n) `mult` (n `divN` o)) `add` ((m `modN` n) `divN` o)) `mult` o
        ? divides_mod_eqs m n o     === m                                                                   *** QED


{-@ divides_mod :: m:N -> {n:N | n != Z} -> {o: N | o != Z && divides o n && divides o (modN m n)} -> {divides o m} @-}
divides_mod :: N -> N -> N -> Proof
divides_mod m n o = divides_def_exists o n ? divides_def_exists o (m `modN` n) ? divides_mod_concl m n o ? divides_def_exists o m

{-@ reflect gcdN @-}
{-@ gcdN :: m:N -> n:N -> {o: N | o != Z} / [toInt m + toInt n] @-} -- {o: N | (geN m n && m != Z && n != Z => (toInt o < toInt m && toInt o < toInt n)) && (leN m n && m != Z && n != Z => (toInt o < toInt m && toInt o < toInt n))}
gcdN :: N -> N -> N
gcdN Z Z = one
gcdN Z n = n
gcdN m Z = m
gcdN m n 
            | m `geN` n && toInt (m `modN` n) < toInt m = gcdN (m `modN` n) n
            | m `eqN` n = m
            | m `leN` n && toInt (n `modN` m) < toInt n = gcdN m (n `modN` m)
            | otherwise = one

{-@ gcd_def_ge :: m:N -> n:N -> {geN m n && n != Z => gcdN m n == gcdN (modN m n) n} @-}
gcd_def_ge :: N -> N -> Proof
gcd_def_ge Z _ = trivial
gcd_def_ge m Z = trivial
gcd_def_ge m n 
            | m `geN` n = termination_cases_lemma m n ? (gcdN m n === gcdN (m `modN` n) n *** QED)
            | m `eqN` n = geN_irreflexive m n
            | m `leN` n = geN_anti_comm m n
            | otherwise = ge_eq_le_exhaustive m n

{-@ gcd_def_le :: m:N -> n:N -> {leN m n && m != Z => gcdN m n == gcdN m (modN n m)} @-}
gcd_def_le :: N -> N -> Proof
gcd_def_le Z _ = trivial
gcd_def_le m Z = trivial
gcd_def_le m n 
            | m `geN` n = geN_anti_comm n m
            | m `eqN` n = geN_irreflexive m n
            | m `leN` n = termination_cases_lemma n m ? (gcdN m n === gcdN m (n `modN` m) *** QED)
            | otherwise = ge_eq_le_exhaustive m n

{-@ gcd_symm :: m:N -> n:N -> {gcdN m n == gcdN n m} / [toInt m + toInt n] @-}
gcd_symm :: N -> N -> Proof
gcd_symm Z Z = trivial
gcd_symm Z n = trivial
gcd_symm m Z = trivial
gcd_symm m n 
            | m `geN` n = termination_cases_lemma m n ? (gcdN m n === gcdN (m `modN` n) n ? gcd_symm (m `modN` n) n === gcdN n (m `modN` n) ? gcd_def_le n m === gcdN n m *** QED)
            | m `eqN` n = eq_equal m n
            | m `leN` n = termination_cases_lemma n m ? (gcdN m n === gcdN m (n `modN` m) ? gcd_symm m (n `modN` m) === gcdN (n `modN` m) m ? gcd_def_ge n m === gcdN n m *** QED)
            | otherwise = ge_eq_le_exhaustive m n


{-@ termination_cases_lemma :: m:N -> {n:N | n != Z && geN m n} -> {toInt (modN m n) < toInt m} @-}
termination_cases_lemma :: N -> N-> Proof
termination_cases_lemma m n 
            | m `geN` n =   ge_geq m n ? (m `modN` n ? subt_mod (m `subt` n) === (m `subt` n) `modN` n *** QED)
                            ? (leN (m `subt` n) m ? subt_leN m n === True *** QED)
                            ? (leN (modN m n) m ==! True *** QED)
                            ? ge_measure m (modN m n)
            | m `eqN` n = geN_irreflexive m n
            | m `leN` n = geN_anti_comm m n
            | otherwise = ge_eq_le_exhaustive m n

-- Definition lemmas for gcdN:
{-@ gcdN_ge :: m:N -> {n:N | geN m n && n != Z} -> {gcdN m n == gcdN (modN m n) n} @-}
gcdN_ge :: N-> N-> Proof
gcdN_ge m n 
            | m `geN` n = gcdN m n ? termination_cases_lemma m n === gcdN (modN m n) n *** QED
            | m `eqN` n = geN_irreflexive m n
            | m `leN` n && toInt (n `modN` m) < toInt n = geN_anti_comm m n
            | otherwise = trivial

{-@ gcdN_le :: m:N -> {n:N | leN m n && m != Z} -> {gcdN m n == gcdN m (modN n m)} @-}
gcdN_le :: N-> N-> Proof
gcdN_le m n 
            | m `geN` n = geN_anti_comm m n
            | m `eqN` n = geN_irreflexive m n
            | m `leN` n = gcdN m n ? termination_cases_lemma n m === gcdN m (modN n m)   *** QED
            | otherwise = trivial

{-@ gcd_post_1_lemma :: m:N -> {n:N | (gcdN m n) != Z && geN m n && n != Z && toInt (modN m n) < toInt m && (gcdN (modN m n) n != Z => (divides (gcdN (modN m n) n) (modN m n) && divides (gcdN (modN m n) n) n))} -> {divides (gcdN m n) m && divides (gcdN m n) n} @-}
gcd_post_1_lemma :: N -> N -> Proof
gcd_post_1_lemma m n = gcdN_ge m n ? divides_mod m n (gcdN m n)

{-@ gcd_post_1 :: m:N -> n:N -> {gcdN m n != Z => (divides (gcdN m n) m && divides (gcdN m n) n)} / [toInt m + toInt n] @-}
gcd_post_1 :: N -> N -> Proof
gcd_post_1 Z Z = one === gcdN Z Z *** QED
gcd_post_1 m Z = (m === gcdN m Z *** QED) ? divides_zero m ? divides_self m
gcd_post_1 Z n = (n === gcdN Z n *** QED) ? divides_zero n ? divides_self n
gcd_post_1 m n 
            | gcdN m n == Z = trivial
            | m `geN` n = termination_cases_lemma m n ? gcd_post_1 (m `modN` n) n ? gcd_post_1_lemma m n
            | m `eqN` n = divides_eqN m n
            | m `leN` n = termination_cases_lemma n m ? gcd_post_1 m (n `modN` m) ? gcd_symm m n ? gcd_post_1_lemma n m
            | otherwise = ge_eq_le_exhaustive m n
