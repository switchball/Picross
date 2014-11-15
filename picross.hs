import Data.List (transpose, intersperse)
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
build n x = take n (repeat x)

-- build a list with ns seperate element x, divided by one y
buildseq ns x y = concat $ intersperse [y] (map (\n->build n x) ns) 

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
createSeq = id

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

--noname :: ([Sequence],[Sequence]) -> [[Disc]]
noname (v,h) = createDisc (length h) (length v)

uncertainty :: [[Disc]] -> Int
uncertainty = count2d Un 

-- generate a list of [Disc], which contain n elements and satisfy *scan* ds = seq
generate       :: Int -> Sequence -> [[Disc]]
generate n sq = [[Oc,Va,Oc,Oc,Va],[Oc,Va,Va,Oc,Oc],[Va,Oc,Va,Oc,Oc]]

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
applyRule []  ds = validate ds (build n Va) where n = length ds
applyRule [m] ds
  | m == 0  = validate ds (build n Va)
  | m == n  = validate ds (build n Oc)
  | 2*m > n = validate ds (build (n-m) Un ++ build (2*m-n) Oc ++ build (n-m) Un ) 
    where n = length ds
-- for possible situation, generate a list, validate them, then evidence them.
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