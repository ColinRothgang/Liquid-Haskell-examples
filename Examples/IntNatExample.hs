{-# OPTIONS_GHC -fplugin=LiquidHaskell #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--diff" @-}
-- {-# LANGUAGE GADTs #-}

{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PackageImports #-}
module IntNatExample where

{- HLINT ignore -}
import Language.Haskell.Liquid.ProofCombinators
import Prelude

{-@ type N = {v: Int | v >= 0} @-}

{-@ reflect suc @-}
{-@ suc :: n:N -> N @-}
suc :: Int -> Int
suc n = 1 + n

-- Addition of natural number and related lemmas:

-- Addition definition lemmas:
{-@ add_zero_l :: n:N -> {0 + n = n} @-}
add_zero_l :: Int -> Proof
add_zero_l n = trivial

{-@ add_suc_l :: m:N -> n:N -> {suc (m + n) = (suc m) + n} @-}
add_suc_l :: Int -> Int -> Proof
add_suc_l m n = trivial

-- | Addition with right zero
{-@ add_zero_r :: n:N -> {n + 0 = n} @-}
add_zero_r :: Int -> Proof
add_zero_r n = trivial

-- | Addition with right successor.
{-@ add_suc_r :: m:N -> n:N -> {suc (m + n) = m + (suc n)} @-}
add_suc_r :: Int -> Int -> Proof
add_suc_r m n = trivial

-- | Addition commutes
{-@ add_comm :: m:N -> n:N -> {m + n == n + m} @-}
add_comm :: Int -> Int -> Proof
add_comm m n = trivial

-- | Addition is associative
{-@ add_assoc :: m:N -> n:N -> o:N -> {m + (n + o) == (m + n) + o} @-}
add_assoc :: Int -> Int -> Int -> Proof
add_assoc m n o = trivial

{-@ add_mono_r :: m:N -> n:N -> {(m + n) >= m && (n > 0 => (m + n) > m)}  @-}
add_mono_r :: Int -> Int -> Proof
add_mono_r m n = trivial

{-@ add_mono_l :: m:N -> n:N -> {(m + n) >= n && (m > 0 => (m + n) > n)}  @-}
add_mono_l :: Int -> Int -> Proof
add_mono_l m n = trivial


-- Multiplicatio of natural numbers and related lemmas:

-- Multiplication definition lemmas:
{-@ mult_zero_l :: n:N -> {0 * n = 0} @-}
mult_zero_l :: Int -> Proof
mult_zero_l n = trivial

{-@ mult_suc_l :: m:N -> n:N -> {(suc m) * n = n + (m * n)} @-}
mult_suc_l :: Int -> Int-> Proof
mult_suc_l m n = trivial

-- | Multiplication with right zero
{-@ mult_zero_r :: n:N -> {n * 0 = 0} @-}
mult_zero_r :: Int -> Proof
mult_zero_r n = trivial

-- | Multiplication with right successor
{-@ mult_suc_r :: n:N -> m:N -> {n * (suc m) = n + (n *  m)} @-}
mult_suc_r :: Int -> Int-> Proof
mult_suc_r m n = trivial

-- | Multiplication with right 1
{-@ mult_1_r :: n:N -> {n * 1 == n} @-}
mult_1_r :: Int -> Proof
mult_1_r n = trivial

-- | Multiplication with left 1
{-@ mult_1_l :: n:N -> {1 * n == n} @-}
mult_1_l :: Int -> Proof
mult_1_l n = add_zero_r n 

-- | Addition distributes over right multiplication
{-@ add_dist_rmult:: m:N -> n:N -> o:N -> {(m + n) * o == (m * o) + (n *  o) } @-}
add_dist_rmult :: Int -> Int -> Int -> Proof
add_dist_rmult m n o = trivial


-- | Addition distributes over left multiplication
{-@ add_dist_lmult:: m:N -> n:N -> o:N -> {m * (n + o) == (m * n) + (m * o) } @-}
add_dist_lmult :: Int -> Int -> Int -> Proof
add_dist_lmult m n _ = mult_zero_r m

{-@ mult_assoc :: m:N -> n:N -> o:N -> {(m * n) * o == m * (n *  o)} @-}
mult_assoc :: Int -> Int -> Int -> Proof
mult_assoc m n o = trivial

{-@ ge_zero :: n:N -> {n >= 0 && n != 0 => n > 0} @-}
ge_zero :: Int -> Proof
ge_zero n = trivial

{-@ mult_zero :: m:N -> n:N -> {m != 0 && n != 0 => (m * n) >= n && (m * n) >= m && (m * n) >= 1} @-}
mult_zero :: Int -> Int -> Proof
mult_zero m n = trivial


-- Subtraction of natural numbers and related lemmas:

-- | subtraction of natural numbers, only works if subtracting from a number greater or equal to the number we subtract from it
{-@ reflect subt @-}
{-@ subt :: m:N -> {n:N | m >= n} -> {o:N | o == m - n && n != 0 => o < m} @-}
subt :: Int -> Int -> Int
subt m n = m - n

-- | subtracting a number from itself yields 0
{-@ subt_self :: m:N -> n:N -> {m == n ==> subt m n == 0} @-}
subt_self :: Int -> Int -> Proof
subt_self m n = trivial

-- | adding and then subtracting a number is identity
{-@ add_subt :: m:N -> n:N -> {subt (m + n) n = m }@-}
add_subt :: Int -> Int -> Proof
add_subt m n = trivial

{-@ subt_suc_l :: m:N -> {n:N | m >= n} -> {subt (suc m) n == suc (subt m n)} @-}
subt_suc_l :: Int -> Int-> Proof
subt_suc_l m n = trivial

-- | subtraction yields a smaller number
{-@ subt_leq :: m:N -> {n:N | m >= n} -> {m >= (subt m n) && n != 0 => m > (subt m n)} @-}
subt_leq :: Int -> Int -> Proof
subt_leq m n = trivial


-- modulo and division operators and their properties:

-- | modulo operation for natural numbers
{-@ reflect modN @-}
{-@ modN :: m:N -> {n:N | n != 0} -> {o:N | o < n && o <= m} @-}
modN ::Int -> Int -> Int
modN m n
            | m < n = m
            | m == n = 0
            | m > n = modN (subt m n) n
            | otherwise = 0

-- | Definition lemmas:
-- | Lemma: m < n => m mod n = m
{-@ ineffective_mod :: m:N -> {n:N | n != 0} -> {m < n ==> modN m n = m} @-}
ineffective_mod :: Int -> Int -> Proof
ineffective_mod m n 
            | m < n = modN m n === m *** QED
            | otherwise = trivial

{-@ equal_mod :: m:N -> {n:N | n != 0} -> {m == n ==> modN m n = 0} @-}
equal_mod :: Int -> Int -> Proof
equal_mod m n 
            | m == n = modN m n === 0 *** QED
            | otherwise = trivial

-- | Lemma: m >= n => m mod n == m - n mod n
{-@ subt_mod :: m:N -> {n:N | n != 0 && m >= n} -> {modN (subt m n) n == modN m n} @-}
subt_mod :: Int -> Int -> Proof
subt_mod m n 
            | m == n = (subt m n) `modN` n ? subt_self m n === 0 `modN` n === 0 ? equal_mod m n === m `modN` n  *** QED 
            | otherwise = trivial


{-@ modN_post :: m:N -> {n:N | n != 0} -> {(modN m n) < n} @-}
modN_post :: Int -> Int -> Proof
modN_post m n 
            | m > n = modN_post (subt m n) n
            | m == n = trivial
            | m < n = m `modN` n === m *** QED

{-@ one_mod :: n:N -> {n > 1 ==> modN 1 n == 1} @-}
one_mod :: Int -> Proof
one_mod n 
            | 1 < n = trivial
            | otherwise = trivial

{-@ m_le_n_mod_suc :: m:N -> {n:N | n != 0} -> {n > (suc m) => modN (suc m) n == suc m} @-}
m_le_n_mod_suc :: Int -> Int -> Proof
m_le_n_mod_suc m n = ineffective_mod (suc m) n


-- | Lemma:     m:N -> {n:N | n != 0} -> {n > S (m mod n) => S m mod n == S (m mod n)}
{-@ modN_suc_1:: m:N -> {n:N | n != 0} -> {n > (suc (modN m n)) ==> modN (suc m) n == suc (modN m n)} @-}
modN_suc_1 :: Int -> Int -> Proof
modN_suc_1 m n 
            | not (n > (suc (modN m n))) = trivial
            | m < n = ineffective_mod m n                      
            | m == n = trivial
            | m > n = modN_suc_1 (subt m n) n
            | otherwise = unreachable

{-@ modN_suc_2:: m:N -> {n:N | n != 0 && n == (suc (modN m n))} -> {modN (suc m) n = 0} @-}
modN_suc_2 :: Int -> Int -> Proof
modN_suc_2 m n 
            | not (n == (suc (modN m n))) = trivial
            | m < n = ineffective_mod m n                        
            | m == n =  trivial
            | m > n = modN_suc_2 (subt m n) n
            | otherwise = unreachable


-- | division (without remainder) of natural numbers
{-@ reflect divN @-}
{-@ divN :: m:N -> {n:N | n != 0} -> N @-}
divN :: Int -> Int -> Int
divN m n
            | m > n = suc ((subt m n) `divN` n)
            | m == n = 1
            | otherwise = 0

-- | Lemma: m >= n => m / n == S ((m - n) / n)
{-@ divN_subt :: m:N -> {n:N | n != 0 && m >= n} -> {suc (divN (subt m n) n) == divN m n} @-}
divN_subt :: Int -> Int -> Proof
divN_subt m n 
            | m > n = trivial
            | m == n = subt_self m n
            | m < n = trivial
            | otherwise = unreachable

{-@ divN_zero :: m:N -> {n:N | n != 0 && m < n} -> {divN m n == 0} @-}
divN_zero :: Int -> Int -> Proof
divN_zero m n = m `divN` n === 0 *** QED

{-@ divN_one :: m:N -> {n:N | n != 0 && m == n} -> {divN m n == 1} @-}
divN_one :: Int -> Int -> Proof
divN_one m n 
            | m > n = trivial
            | m == n = m `divN` n === 1 *** QED
            | otherwise = trivial    

{-@ div_mult :: m:N -> {n:N | n != 0} -> {divN (m * n) n == m} @-}
div_mult 0 n = mult_zero_l n ? divN_zero 0 n
div_mult suc_m n =                              (suc_m * n) `divN` n
                                            === (n + (m * n)) `divN` n
                ? divN_subt (n + (m * n)) n === suc (((n + (m * n)) `subt` n) `divN` n)
                ? add_subt (m * n) n        === suc ((m * n) `divN` n)
                ? div_mult m n              === suc m                           *** QED
    where
        m = suc_m `subt` 1
    

-- n > S (m mod n) => S m / n == m / n
{-@ divN_suc_1:: m:N -> {n:N | n != 0 && n > (suc (modN m n))} -> {divN (suc m) n == divN m n} @-}
divN_suc_1 :: Int -> Int -> Proof
divN_suc_1 m n 
            | m > n = divN_suc_1 (subt m n) n
            | m == n = trivial
            | m < n = trivial
            | otherwise  = unreachable

{-@ divN_suc_2:: m:N -> {n:N | n != 0 && n == (suc (modN m n))} -> {divN (suc m) n = suc (divN m n)} @-}
divN_suc_2 :: Int -> Int -> Proof
divN_suc_2 m n 
            | m > n  = divN_suc_2 (subt m n) n ? subt_mod m n ? divN_subt m n ? divN_subt (suc m) n
            | m == n =                                          (suc m) `divN` n 
                                ? divN_subt (suc m) n       === suc (((suc m) `subt` n) `divN` n) 
                                ? subt_self m n             === suc ((suc 0) `divN` n)
                                ? divN_one 1 n              === suc (m `divN` n)    *** QED
            | m < n && n < suc m = unreachable
            | m < n && n == suc m = (suc m) `divN` n 
                                ? divN_one (suc m) n        === 1
                                ? divN_zero m n             === suc (m `divN` n)    *** QED
            | m < n && n > suc m = ineffective_mod m n
            | otherwise  = unreachable

-- | division with remainder is correct
{-@ divModN :: m:N -> {n:N | n != 0} -> {(modN m n) + ((divN m n) * n) == m} @-}
divModN :: Int -> Int -> Proof
divModN 0 n = trivial
divModN suc_m n
                    | n > suc (m `modN` n) =                (suc_m `modN` n) + ((suc_m `divN` n) * n)
                                                        === ((suc m) `modN` n) + ((suc_m `divN` n) * n)
                    ? modN_suc_1 m n ? divN_suc_1 m n   === (suc (m `modN` n)) + ((suc_m `divN` n) * n)
                                                        === suc (m `modN` n) + ((suc_m `divN` n) * n)
                                ? divModN m n           === suc m                            *** QED
                                
                    | n == (suc (m `modN` n)) =             (suc_m `modN` n) + ((suc_m `divN` n) * n)
                                ? modN_suc_2 m n        === 0 + ((suc_m `divN` n) * n)
                                ? divN_suc_2 m n        === 0 + ((suc (m `divN` n)) * n)
                                                        === (suc (m `divN` n)) * n
                            ? mult_suc_l (m `divN` n) n === n + ((m `divN` n) * n)
                                                        === (suc (m `modN` n)) + ((m `divN` n) * n)
                                                        === suc ((m `modN` n) + ((m `divN` n) * n))
                                ? divModN m n           === suc m                            *** QED
                    | n < (suc (m `modN` n)) = modN_post m n
                    | otherwise = unreachable
    where 
        m = suc_m `subt` 1

{-@ reflect divides @-}
{-@ divides :: {m:N | m != 0} -> n:N -> o: Bool @-}
divides :: Int -> Int -> Bool
divides m n = (n `modN` m) == 0

{-@ divides_def :: {m:N | m != 0} -> n:N -> {divides m n <=> ((modN n m) == 0)} @-}
divides_def :: Int -> Int -> Proof
divides_def m n = divides m n === (n `modN` m) == 0  === (n `modN` m) == 0   *** QED

{-@ divides_exists :: {m:N | m != 0} -> {n:N | divides m n} -> {(divN n m) * m == n} @-}
divides_exists :: Int -> Int -> Proof
divides_exists m n =                    n
                ? divModN n m       === (n `modN` m) + ((n `divN` m) * m)
                ? divides_def m n   === 0 + ((n `divN` m) * m)
                                    === (n `divN` m) * m           *** QED

{-@ exists_divides_lem :: {m:N | m != 0} -> {n:N | (divN n m) * m == n} -> {(modN n m) + ((divN n m) * m) == (divN n m) * m} @-}
exists_divides_lem :: Int -> Int -> Proof
exists_divides_lem m n =            (n `modN` m) + ((n `divN` m) * m)
                ? divModN n m   === n
                                === ((n `divN` m) * m)       *** QED

{-@ exists_divides :: {m:N | m != 0} -> {n:N | (divN n m) * m == n} -> {divides m n} @-}
exists_divides :: Int -> Int -> Proof
exists_divides m n = divides_def m n ?                      (0
        ? exists_divides_lem m n    ? subt_self ((n `modN` m) + ((n `divN` m) * m)) ((n `divN` m) * m)
                                                        === ((n `modN` m) + ((n `divN` m) * m)) `subt` ((n `divN` m) * m)
        ? add_subt (n `modN` m) ((n `divN` m) * m)      === n `modN` m              *** QED)

{-@ divides_def_exists :: {m:N | m != 0} -> n:N -> {divides m n <=> (divN n m) * m == n} @-}
divides_def_exists :: Int -> Int -> Proof
divides_def_exists m n 
                | (n `divN` m) * m == n = exists_divides m n
                | divides m n = divides_exists m n
                | otherwise = trivial

{-@ divides_self :: {n:N | n != 0} -> {divides n n} @-}
divides_self :: Int -> Proof
divides_self n = divides_def n n ? ((n `modN` n)    ? subt_mod n n  === (n `subt` n) `modN` n
                                                    ? subt_self n n === 0 `modN` n
                                                                    === 0           *** QED)

{-@ divides_zero :: {n:N | n != 0} -> {divides n 0} @-}
divides_zero :: Int -> Proof
divides_zero n = (0 `modN` n     === 0   *** QED) ? divides_def n 0

{-@ divides_eqN :: {m:N | m != 0} -> {n:N | m == n} -> {divides m n} @-}
divides_eqN :: Int -> Int -> Proof
divides_eqN m n = divides_self m

{-@ divides_mod_eqs :: m:N -> {n:N | n != 0} -> {o:N | o != 0 && (divN n o) * o == n && (divN (modN m n) o) * o == (modN m n)} -> {(((divN m n) * (divN n o)) + (divN (modN m n) o)) * o == m} @-}
divides_mod_eqs :: Int -> Int -> Int -> Proof
divides_mod_eqs m n o =             m
                ? divModN m n   === r + (q * n)
                                === r + (q * (divN n o) * o)
                                === (r `divN` o) * o + q * (divN n o) * o
                                === ((r `divN` o) + q * (divN n o)) * o   *** QED
    where
        q = m `divN` n
        r = m `modN` n


{-@ divides_mod_ass :: m:N -> {n:N | n != 0} -> {o:N | o != 0 && (divN n o) * o == n && (divN (modN m n) o) * o == (modN m n)} -> {((divN m n) * (divN n o)) + (divN (modN m n) o) == divN m o} @-}
divides_mod_ass :: Int -> Int -> Int -> Proof
divides_mod_ass m n o =                                     m `divN` o
                                ? divides_mod_eqs m n o === (((q * (n `divN` o)) + (r `divN` o)) * o) `divN` o
    ? div_mult ((q * (n `divN` o)) + (r `divN` o)) o    === (q * (n `divN` o)) + (r `divN` o)                *** QED
    where
        q = m `divN` n
        r = m `modN` n

{-@ divides_mod_concl :: m:N -> {n:N | n != 0} -> {o:N | o != 0 && (divN n o) * o == n && (divN (modN m n) o) * o == (modN m n)} -> {(divN m o) * o == m} @-}
divides_mod_concl :: Int -> Int -> Int -> Proof
divides_mod_concl m n o =               (m `divN` o) * o
        ? divides_mod_ass m n o     === (((m `divN` n) * (n `divN` o)) + ((m `modN` n) `divN` o)) * o
        ? divides_mod_eqs m n o     === m                                                                   *** QED


{-@ divides_mod :: m:N -> {n:N | n != 0} -> {o:N | o != 0 && divides o n && divides o (modN m n)} -> {divides o m} @-}
divides_mod :: Int -> Int -> Int -> Proof
divides_mod m n o = divides_def_exists o n ? divides_def_exists o (m `modN` n) ? divides_mod_concl m n o ? divides_def_exists o m

{-@ reflect gcdN @-}
{-@ gcdN :: m:N -> n:N -> {o:N | o != 0} / [m + n] @-}
gcdN :: Int -> Int -> Int
gcdN 0 0 = 1
gcdN 0 n = n
gcdN m 0 = m
gcdN m n 
            | m > n = gcdN (m `modN` n) n
            | m == n = m
            | m < n = gcdN m (n `modN` m)
            | otherwise = 1

{-@ gcd_def_ge :: m:N -> n:N -> {m > n && n != 0 => gcdN m n == gcdN (modN m n) n} @-}
gcd_def_ge :: Int -> Int -> Proof
gcd_def_ge 0 _ = trivial
gcd_def_ge m 0 = trivial
gcd_def_ge m n 
            | m > n = (gcdN m n === gcdN (m `modN` n) n *** QED)
            | m == n = trivial
            | m < n = trivial
            | otherwise = unreachable

{-@ gcd_def_le :: m:N -> n:N -> {m < n && m != 0 => gcdN m n == gcdN m (modN n m)} @-}
gcd_def_le :: Int -> Int -> Proof
gcd_def_le 0 _ = trivial
gcd_def_le m 0 = trivial
gcd_def_le m n 
            | m > n = trivial
            | m == n = trivial
            | m < n = (gcdN m n === gcdN m (n `modN` m) *** QED)
            | otherwise = unreachable

{-@ gcd_symm :: m:N -> n:N -> {gcdN m n == gcdN n m} / [m + n] @-}
gcd_symm :: Int -> Int -> Proof
gcd_symm 0 0 = trivial
gcd_symm 0 n = trivial
gcd_symm m 0 = trivial
gcd_symm m n 
            | m > n = (gcdN m n === gcdN (m `modN` n) n ? gcd_symm (m `modN` n) n === gcdN n (m `modN` n) ? gcd_def_le n m === gcdN n m *** QED)
            | m == n = trivial
            | m < n = (gcdN m n === gcdN m (n `modN` m) ? gcd_symm m (n `modN` m) === gcdN (n `modN` m) m ? gcd_def_ge n m === gcdN n m *** QED)
            | otherwise = unreachable

-- Definition lemmas for gcdN:
{-@ gcdN_ge :: m:N -> {n:N | m > n && n != 0} -> {gcdN m n == gcdN (modN m n) n} @-}
gcdN_ge :: Int-> Int-> Proof
gcdN_ge m n 
            | m > n     = gcdN m n  === gcdN (modN m n) n *** QED
            | m == n    = trivial
            | m < n     = trivial
            | otherwise = unreachable

{-@ gcdN_le :: m:N -> {n:N | m < n && m != 0} -> {gcdN m n == gcdN m (modN n m)} @-}
gcdN_le :: Int-> Int-> Proof
gcdN_le m n 
            | m > n     = trivial
            | m == n    = trivial
            | m < n     = gcdN m n === gcdN m (modN n m)   *** QED
            | otherwise = unreachable

{-@ gcd_post_1_lemma :: m:N -> {n:N | m > n && n != 0 && (gcdN (modN m n) n != 0 => (divides (gcdN (modN m n) n) (modN m n) && divides (gcdN (modN m n) n) n))} -> {divides (gcdN m n) m && divides (gcdN m n) n} @-}
gcd_post_1_lemma :: Int -> Int -> Proof
gcd_post_1_lemma m n = gcdN_ge m n ? divides_mod m n (gcdN m n)

{-@ gcd_post_1 :: m:N -> n:N -> {divides (gcdN m n) m && divides (gcdN m n) n} / [m + n] @-}
gcd_post_1 :: Int -> Int -> Proof
gcd_post_1 0 0 = trivial
gcd_post_1 m 0 = (m === gcdN m 0 *** QED) ? divides_zero m ? divides_self m
gcd_post_1 0 n = (n === gcdN 0 n *** QED) ? divides_zero n ? divides_self n
gcd_post_1 m n 
            | gcdN m n == 0 = trivial
            | m > n = gcd_post_1 (m `modN` n) n ? gcd_post_1_lemma m n
            | m == n = divides_eqN m n
            | m < n = gcd_post_1 m (n `modN` m) ? gcd_symm m n ? gcd_post_1_lemma n m
            | otherwise = unreachable
