--Casey Nold
-- nold@pdx.edu
module HW5 where

import Data.List
import Test.HUnit(Test(TestCase,TestList),assertEqual,runTestTT)
import Test.QuickCheck
import Test.QuickCheck.Test(isSuccess)

-- inductive proofs
-- Prove --> map f x ++ map f y == map f( x++y)
-- Rules: 1) map f [] = []  
--        2) map f(x:xs) = f(x):(map f xs)
--        3) [] ++ [] == []
-- Base Case: map f x ++ map f y == map f(x++y)
-- A0: map f [] ++ map f [] == map f ([] ++[])
--     [] ++ [] == map f ([])   **by rule 1
--        []    ==  []          ** by rule 1 and rule 3
--
--An:   map f x ++ map f y == map f (x++y)
--An+1: map f(x:xs) ++ map f(y:ys) == map f (x:xs ++ y:ys)
--      f(x):map(xs) ++ f(y):map(ys) == map f( x:xs ++ y:ys)          ** by rule 2
--      f(x):map(xs) ++ f(y):map(ys) ==  f(x):map(xs) ++ f(y):map(ys) ** by applying map
--      map f(x:xs) ++ map f(y:ys) == map f(x:xs) ++ map f(y:ys)      ** by rule 2 backwards & IH
--      
--A ⊥ : map f(⊥) ++ mapf(⊥)  ==  map f(⊥ ++ ⊥)
--        ⊥ ++ ⊥     ==   map f(⊥)          ** by map being strict on its list & append being left strict
--               ⊥   == ⊥                 ** by map being strict on its list & append being left strict
--                      QED
-- *****************************************************************************
-- Prove --> length(zip xs ys) == length(min xs ys)
-- Rules: 1) zip [] [] = []     2) min [] [] = []
--        3) length [] = 0      4) zip(x:xs y:ys) = (x,y):zip(xs ys)
--        5) min x:xs y:ys == 1 + min xs ys
--        6) length(x:xs y:ys) = 1+ length(xs ys)
--        7) length(min xs ys) = length xs `min` length ys
-- A0:  length(zip[] [])  == length(min [][])
--      length(zip [] []) == length []         ** by rule 2
--             length []  == length []         ** by rule 1
--                    0   ==  0                ** by rule 3

--An:       length(zip xs ys)  == length(min xs ys)
--An+1  length(zip x:xs y:ys)  == length(min x:xs y:ys)
--      length((x,y)zip(xs,ys) == length(min x:xs y:ys)                ** by rule 4  
--      1+ length(zip xs ys)   == length x:xs `min` length y:ys        ** by rule 7
--      1+ length(zip xs ys)   == 1 + length xs `min` 1 + length ys    ** by rule 6
--      1+ length(zip xs ys)   == 1+ length( min xs ys)                ** by IH
--
--A ⊥:  length(zip(⊥ ⊥))       == length(min ⊥ ⊥)                      ** by zip & min being strict 
--      length(⊥)              == length(⊥)                            ** by length being strict
--               ⊥             ==    ⊥
--                        QED
--quickCheck test--> results at the end of file.
zipLen :: [Int] -> [Int] -> Int
zipLen xs ys =  length(zip xs ys)

lenMin :: [Int] ->[Int] -> Int
lenMin xs ys =  length(min xs ys)
prop_lz xs ys = length (zip xs ys) == length(min xs ys)

{- *************************************************** -}
data Bit = O | I  deriving (Eq,Show, Ord)

type BinNum = [Bit]

toBinNum  :: Integer -> BinNum
toBinNum n | n == 0 = []
           | n `mod` 2 == 1 = I :toBinNum(halfOfN)
           | n `mod` 2 == 0 = O :toBinNum(halfOfN)
             where halfOfN = n `div` 2

inc :: BinNum -> BinNum
inc []      = [I]
inc [I]     = O:[I]
inc [O]     = I:[O]
inc (O:ds)  = [I] ++ ds
inc (I:ds)  = O : inc ds

add :: BinNum -> BinNum -> BinNum
add []     ds     =  [] ++ ds
add ds     []     =  ds ++ [] 
add (O:ds) (e:es) = O : add ds es
add (I:ds) (O:es) = I : add ds es
add (I:ds) (I:es) = O : inc(add (ds) (es)) 

-- new algorithm for adding binary numbers
add2 :: BinNum ->BinNum -> BinNum
add2 (x:xs) (y:ys) | (x:xs) == []     && (y:ys) /= [] = y: add2 [] ys 
                   | (x:xs) /= []     && (y:ys) == [] = x: add2 xs []
                   | (x:xs) == []     && (y:ys) == [] =    add2 [] []
                   | x:xs == (O:xs) && y:ys == (O:ys) = O: add xs ys
                   | x:xs == (I:xs) && y:ys == (O:ys) = I: add xs ys
                   | x:xs == (O:xs) && y:ys == (I:ys) = I: add xs ys
                   | x:xs == (I:xs) && y:ys == (I:ys) = O: inc(add(xs)(ys))


-- Testing for the add & add2 functions
testOne   = assertEqual "empty plus bin 1"     (add [I,O] [I,O]) [O,I,O]
testTwo   = assertEqual "bin 3 plus bin 1"     (add [I,I] [I,O]) [O,O,I]
testThree = assertEqual "bin 6 plus bin 6"     (add [O,I,I] [O,I,I]) [O,O,I,I]
testFour  = assertEqual "bin 10 plus bin 2"    (add [O,I,O,I][O,I]) [O,O,I,I]
testFive  = assertEqual "zero plus zero"       (add [O] [O]) [O]
testSix   = assertEqual "bin 7 plus bin 2"     (add [I,I,I] [O,I,O]) [I,O,O,I]
testSeven = assertEqual "bin 8 plus bin 10"    (add [O,O,O,I][O,I,O,I]) [O,O,O,O,I]
testEight = assertEqual "bin 16 plus bin 1024" (add [O,O,O,O,I][O,O,O,O,O,O,O,O,O,O,I]) [ O,O,O,O,I,O,O,O,O,O,I]
testNine  = assertEqual "bin 24 plus bin 48"   (add [O,O,O,I,I] [O,O,O,O,I,I]) [O,O,O,I,O,O,I]
testTen   = assertEqual "bin 256 plus 512"     (add [O,O,O,O,O,O,O,O,I] [O,O,O,O,O,O,O,O,O,I]) [O,O,O,O,O,O,O,O,I,I]
tests_add = TestList[ TestCase testOne, TestCase testTwo, TestCase testThree,TestCase testFour, TestCase testFive, 
                  TestCase testSix, TestCase testSeven, TestCase testEight, TestCase testNine,TestCase testTen]

-- add2 tests
testOne2   = assertEqual "bin 1 plus bin 1"     (add2 [I,O] [I,O]) [O,I,O]
testTwo2   = assertEqual "bin 3 plus bin 1"     (add2 [I,I] [I,O]) [O,O,I]
testThree2 = assertEqual "bin 6 plus bin 6"     (add2 [O,I,I] [O,I,I]) [O,O,I,I]
testFour2  = assertEqual "bin 10 plus bin 2"    (add2 [O,I,O,I][O,I]) [O,O,I,I]
testFive2  = assertEqual "zero plus zero"       (add2 [O] [O]) [O]
testSix2   = assertEqual "bin 7 plus bin 2"     (add2 [I,I,I] [O,I,O]) [I,O,O,I]
testSeven2 = assertEqual "bin 8 plus bin 10"    (add2 [O,O,O,I][O,I,O,I]) [O,O,O,O,I]
testEight2 = assertEqual "bin 16 plus bin 1024" (add2 [O,O,O,O,I][O,O,O,O,O,O,O,O,O,O,I]) [ O,O,O,O,I,O,O,O,O,O,I]
testNine2  = assertEqual "bin 24 plus bin 48"   (add2 [O,O,O,I,I] [O,O,O,O,I,I]) [O,O,O,I,O,O,I]
testTen2   = assertEqual "bin 256 plus 512"     (add2 [O,O,O,O,O,O,O,O,I] [O,O,O,O,O,O,O,O,O,I]) [O,O,O,O,O,O,O,O,I,I]
tests_add2 = TestList[ TestCase testOne2, TestCase testTwo2, TestCase testThree2, TestCase testFour2, TestCase testFive2, 
                  TestCase testSix2, TestCase testSeven2, TestCase testEight2, TestCase testNine2,TestCase testTen2]

-- main that runs the tests
main = runTestTT (TestList[tests_add, tests_add2]) 
{- *** below is the prelude output from the tests
 - *HW5> main
 - Cases: 20  Tried: 20  Errors: 0  Failures: 0
 - Counts {cases = 20, tried = 20, errors = 0, failures = 0}
 -*HW5> quickCheck prop_lz 
 +++ OK, passed 100 tests.
 -}
