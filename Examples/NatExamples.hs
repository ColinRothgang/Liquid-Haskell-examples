{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--diff" @-}
-- {-# LANGUAGE GADTs #-}

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PackageImports #-}
module NatExamples where

{- HLINT ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude

{-@ data N [toInt] = Z | Suc N @-}
data N = Z | Suc N

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
{-@ mult_one_r :: n:N -> {mult n one = n} @-}
mult_one_r :: N -> Proof
mult_one_r Z    = trivial
mult_one_r (Suc n) = mult_one_r n

-- | Multiplication with left one
{-@ mult_one_l :: n: N -> {mult one n = n} @-}
mult_one_l :: N -> Proof
mult_one_l n = add_zero_r n 

-- | Addition distributes over right multiplication
{-@ add_dist_rmult:: m: N -> n: N -> o: N -> {mult (add m n) o = add (mult m o) (mult n o) } @-}
add_dist_rmult :: N -> N -> N -> Proof
add_dist_rmult Z _ _ = trivial
add_dist_rmult (Suc m) n o = add_dist_rmult m n o ? add_assoc o (mult m o) (mult n o)


-- | Addition distributes over left multiplication
{-@ add_dist_lmult:: m: N -> n: N -> o: N -> {mult m (add n o) = add (mult m n) (mult m o) } @-}
add_dist_lmult :: N -> N -> N -> Proof
add_dist_lmult m Z _ = mult_zero_r m
add_dist_lmult m (Suc n) o  = mult_suc_r m (add n o) 
                            ? add_dist_lmult m n o 
                            ? add_assoc m (mult m n) (mult m o) 
                            ? mult_suc_r m n

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

{-@ ge_geq_suc :: m: N -> n: N -> { geN m n == geqN m (Suc n)} @-}
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

-- useful lemma
{-@ geqN_suc_l:: m: N -> {n: N | geqN m n} -> {geqN (Suc m) n} @-}
geqN_suc_l :: N -> N -> Proof
geqN_suc_l (Suc m) (Suc n) = geqN_suc_l m n
geqN_suc_l (Suc m) Z = trivial
geqN_suc_l Z Z = trivial
geqN_suc_l Z (Suc n) = trivial

-- | geqN = geN union eqN
{-@ geqN_geN_eqN:: m: N -> n: N -> { geqN m n <=> geN m n || eqN m n} @-}
geqN_geN_eqN:: N -> N -> Proof
geqN_geN_eqN Z Z = trivial
geqN_geN_eqN (Suc m) Z = trivial
geqN_geN_eqN Z (Suc n) = trivial
geqN_geN_eqN (Suc m) (Suc n) = geqN_geN_eqN m n

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
{-@ modN :: m:N -> {n:N | n != Z} -> {o:N | o != Z ==> toInt o < toInt n} @-}
modN ::N -> N -> N
modN Z n = Z
modN m n
            | m `geN` n = modN (subt m n) n
            | m `eqN` n = Z
            | m `leN` n = m
            -- it is easy to prove this case is impossible, but without it LH complains about a missing case
            -- we cannot use impossibleValue here as we need to be able to reflect on this function
            | otherwise = Z -- impossibleValue "ge, eq and le are exhaustive"

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

-- n > S (m mod n) => (S (m - n) div n == (m - n) div n) => S m div n == m div n
{-@ divN_suc_1_ge_concl:: m: N -> {n:N | n != Z && geN n (Suc (modN m n)) && divN (Suc (subt m n)) n = divN (subt m n) n && geN m n && geqN m n} -> {divN (Suc (subt m n)) n = divN (subt m n) n => divN (Suc m) n = divN m n} @-}
divN_suc_1_ge_concl :: N -> N -> Proof
divN_suc_1_ge_concl m n = trivial

{-@ divN_suc_1:: m: N -> {n:N | n != Z && geN n (Suc (modN m n))} -> {divN (Suc m) n = divN m n} @-}
divN_suc_1 :: N -> N -> Proof
divN_suc_1 m n 
            | m `geN` n  && m `geqN` n  = divN_suc_1 (subt m n) n ? subt_mod m n ? divN_suc_1_ge_concl m n
            | m `eqN` n = trivial
            | Suc m `eqN` n = trivial
            | otherwise  = trivial

{-@ divN_suc_2:: m: N -> {n:N | n != Z} -> {eqN n (Suc (modN m n)) ==> divN (Suc m) n = Suc (divN m n)} @-}
divN_suc_2 :: N -> N -> Proof
divN_suc_2 m n 
            | m `geN` n  && m `geqN` n = divN_suc_2 (subt m n) n ? subt_mod m n ? divN_suc_1_ge_concl m n
            | m `eqN` n = trivial
            | Suc m `eqN` n = trivial
            | otherwise  = trivial

-- | division with remainder is correct
{-@ divModN :: m:N -> n:N -> {add (modN m n) (mult (divN m n) n) = m} @-}
divModN :: N -> N -> Proof
divModN Z Z = trivial
divModN Z (Suc n) = trivial
divModN (Suc m) n
                   | geN n (Suc (modN m n)) = trivial
                   | otherwise = trivial