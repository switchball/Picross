import Data.List (transpose, intersperse, intercalate)
import Control.Monad

nest :: (t -> t) -> t -> Int -> t
nest f x n
  | n > 0     = nest f (f x) (n-1)
  | n == 0    = x 
  | otherwise = error "nest : n < 0"

nest2 :: (t -> t -> t) -> t -> t -> Int -> t
nest2 g b a n
  | n > 0     = nest2 g (g a b) b (n-1)
  | n == 0    = b
  | otherwise = error "nest2 : n < 0"

count x xs = length $ filter (==x) xs

count2d x xss = sum $ map (count x) xss

-- build a list with n element x
build     :: a -> Int -> [a]
build x n = take n (repeat x)

-- build a 2d-list with ns seperate element x
-- build x [1,0,2] = [[x],[],[x,x]]
buildseq      :: a -> [Int] -> [[a]]
buildseq x ns = map (build x) ns


data Disc = Un|Oc|Va
            deriving (Show,Read,Eq)

discAnd :: Disc -> Disc -> Maybe Disc
--discAnd Nothing _ = Nothing
--discAnd _ Nothing = Nothing
discAnd Un x = Just x
discAnd x Un = Just x
discAnd Oc Oc = Just Oc
discAnd Va Va = Just Va
discAnd Oc Va = Nothing
discAnd Va Oc = Nothing

discOr :: Disc -> Disc -> Disc
--discOr Nothing x = x
--discOr x Nothing = x
discOr Oc Oc = Oc
discOr Va Va = Va
discOr _  _  = Un

createDisc :: Int -> Int -> [[Disc]]
createDisc m = take m . repeat . createDisc1d

createDisc1d :: Int -> [Disc]
createDisc1d n = take n (repeat Un)

createSeq :: [Int] -> Sequence
createSeq =  id

createSeqs :: [[Int]] -> [Sequence]
createSeqs =  id

type Sequence = [Int]
type Sequences = [[Int]]

seq0   = createSeq [0]
seq3   = createSeq [3]
seq5   = createSeq [5]
seq12  = createSeq [1,2]
seq111 = createSeq [1,1,1]
seqs1  = [[1],[1],[5],[1],[1]]
seqs2 = [[1],[1],[5],[1],[1]]

disc1d = createDisc1d 5
disc2d = createDisc 3 3

discSmall = createDisc 5 5
-- == Test Case == --
{- Case No.1 Sprite
   ***
  * * *
  *****
   * *
   * *
-}
seqsHor1 = createSeqs [[3],[1,1,1],[5],[3],[1,1]]
seqsVer1 = createSeqs [[2],[1,3],[4],[1,3],[2]]
hs1      = (seqsHor1,discSmall)
vs1      = (seqsVer1,discSmall)
discCor1 = undefined


--noname :: ([Sequence],[Sequence]) -> [[Disc]]
noname (v,h) = createDisc (length h) (length v)

uncertainty :: [[Disc]] -> Int
uncertainty = count2d Un 

-- insert 2nd list to 1st list in middle
-- merge [x1,x2,x3] [y1,y2,y3] = [x1,y1,x2,y2,x3]
merge                  :: [a] -> [a] -> [a]
merge []        _      = []
merge (x:xs)    []     = [x]
merge [x]       (y:ys) = [x]
merge (x:x':xs) (y:ys) = x:y:(merge (x':xs) ys)

-- solve x_0+x_1+...+x_m = n 
-- where x_1...x_(m-1) >0 and x_0,x_m >= 0
intpartition     :: Int -> Int -> [[Int]]
intpartition n m = map fstval $
                     filter (\s -> sum s <= n) $
                       nest (\z -> concat $ map addval z) intval (m-1)
                       where intval = map (\x->[x]) [0..n]   -- [[0],[1]..[n]]
                             addval = \s -> map (:s) [1..n]  -- map add [1..n] to head of list
                             fstval = \xs -> (n-sum xs):xs   -- add (n-sum xs) to head of list

-- generate a list of [Disc], which contain n elements and satisfy *scan* ds = seq
-- generate 5 [1,2] = [[Oc,Va,Oc,Oc,Va],[Oc,Va,Va,Oc,Oc],[Va,Oc,Va,Oc,Oc]]
generate       :: Int -> Sequence -> [[Disc]]
generate n sq = map (\xss -> concat $ merge xss ocss) vasss
                  where vasss = map (buildseq Va) (intpartition (n - sum sq) (length sq))
                        ocss  = buildseq Oc sq

-- zip two [Disc] with discAnd logic
-- to see the common part or contradiction!
-- Often, 1st param is the known,
--        2nd param is the test one, for currying easily
validate  :: [Disc] -> [Disc] -> Maybe [Disc]
validate  =  zipWithM discAnd

evidence  :: [Disc] -> [Disc] -> [Disc]
evidence  = zipWith discOr

evidenceM :: Maybe [Disc] -> Maybe [Disc] -> Maybe [Disc]
evidenceM Nothing x = x
evidenceM x Nothing = x
evidenceM x y       = (liftM2 evidence) x y

applyRule :: Sequence -> [Disc] -> Maybe [Disc]
-- for simple situation
applyRule []  ds = validate ds (build Va n) where n = length ds
applyRule [m] ds
  | m == 0  = validate ds (build Va n)
  | m == n  = validate ds (build Oc n)
  | 2*m > n = validate ds (build Un (n-m) ++ build Oc (2*m-n) ++ build Un (n-m) ) 
    where n = length ds
-- for complex situation, generate a list, validate them, then evidence them.
applyRule seq ds
  | sum seq + length seq - 1 <= n = foldl evidenceM Nothing (map (validate ds) (generate n seq))
    where n = length ds

partialFill :: ([Sequence], [[Disc]]) -> [Maybe [Disc]]
partialFill = uncurry . zipWith $ applyRule

reduceState :: ([Sequence], [[Disc]]) -> ([Sequence], [Maybe [Disc]])
reduceState x = ((fst x), partialFill x)

{-
solve ((hr,g):(vr,gt):[]) 
  | uncertainty g == 0 = g
  | otherwise          = solve $ [(vr, transpose . snd $ result), result] 
                            where result = reduceState (hr,g)
-}

