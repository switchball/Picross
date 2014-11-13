import Data.List (transpose, intersperse)

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

discAnd :: Disc -> Disc -> Disc
discAnd x Un = x
discAnd Un x = x
discAnd Oc Oc = Oc
discAnd Va Va = Va
discAnd Oc Va = error "Oc and Va = Contradiction!"
discAnd Va Oc = error "Va and Oc = Contradiction!"

discOr :: Disc -> Disc -> Disc
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

seq0 = createSeq [0]
seqs1  = [[1],[1],[5],[1],[1]]
seqs2 = [[1],[1],[5],[1],[1]]

disc1d = createDisc1d 5
disc2d = createDisc 3 3

--noname :: ([Sequence],[Sequence]) -> [[Disc]]
noname (v,h) = createDisc (length h) (length v)

uncertainty :: [[Disc]] -> Int
uncertainty = count2d Un 

applyRule :: Sequence -> [Disc] -> [Disc]
applyRule []  ds = zipWith discAnd ds (build n Va) where n = length ds
applyRule [m] ds
  | m == 0  = zipWith discAnd ds (build n Va)
  | m == n  = zipWith discAnd ds (build n Oc)
  | 2*m > n = zipWith discAnd ds (build (n-m) Un ++ build (2*m-n) Oc ++ build (n-m) Un ) 
    where n = length ds
applyRule seq ds
  | sum seq + length seq - 1 == n = zipWith discAnd ds (buildseq seq Oc Va) where n = length ds


partialFill :: ([Sequence], [[Disc]]) -> [[Disc]]
partialFill = uncurry . zipWith $ applyRule

reduceState :: ([Sequence], [[Disc]]) -> ([Sequence], [[Disc]])
reduceState x = ((fst x), partialFill x)

solve ((hr,g):(vr,gt):[]) 
  | uncertainty g == 0 = g
  | otherwise          = solve $ [(vr, transpose . snd $ result), result] 
                            where result = reduceState (hr,g)