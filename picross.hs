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
hsM1     = (seqsHor1,Just discSmall)
vsM1     = (seqsVer1,Just discSmall)
discCor1 = [[Va,Oc,Oc,Oc,Va],
            [Oc,Va,Oc,Va,Oc],
            [Oc,Oc,Oc,Oc,Oc],
            [Va,Oc,Oc,Oc,Va],
            [Va,Oc,Va,Oc,Va]]


--noname :: ([Sequence],[Sequence]) -> [[Disc]]
noname (v,h) = createDisc (length h) (length v)

uncertainty :: [[Disc]] -> Int
uncertainty = count2d Un 

transform            :: Maybe [[Disc]] -> Maybe [[Disc]]
transform Nothing    = Nothing
transform (Just dss) = Just (transpose dss)

-- insert 2nd list to 1st list in middle
-- merge [x1,x2,x3] [y1,y2,y3] = [x1,y1,x2,y2,x3]
merge                  :: [a] -> [a] -> [a]
merge []        _      = []
merge (x:xs)    []     = [x]
merge [x]       (y:ys) = [x]
merge (x:x':xs) (y:ys) = x:y:(merge (x':xs) ys)

-- solve x_0+x_1+...+x_m = n 
-- where x_1...x_(m-1) >0 and x_0,x_m >= 0
-- current alg notation: T=O(n^m) slow when n^m > 1e6
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
-- to see the whether it has a contradiction!
-- Often, 1st param is the known,
--        2nd param is the test one, for currying easily.
validate  :: [Disc] -> [Disc] -> Maybe [Disc]
validate  =  zipWithM discAnd

-- zip two [Disc] with discOr logic
-- to see the common part, i.e. some position stands still!
-- the method is to be liftM up and to be folded.
evidence  :: [Disc] -> [Disc] -> [Disc]
evidence  = zipWith discOr

-- liftM up the evidence method, to be folded.
-- Notice originally Nothing will case the expr to be Nothing,
-- here due to the logic or, we simplily ignore it.
evidenceM :: Maybe [Disc] -> Maybe [Disc] -> Maybe [Disc]
evidenceM Nothing x = x
evidenceM x Nothing = x
evidenceM x y       = (liftM2 evidence) x y

-- applyRule take a sequence rule and a partial-known [Disc] state,
-- to infer the certain position of [Disc] state.
-- if there is no solution or contradiction, Nothing is returned.
applyRule :: Sequence -> [Disc] -> Maybe [Disc]
-- for simple situation, notice that [] is equivalent to [0]
applyRule []  ds = validate ds (build Va n) where n = length ds
applyRule [m] ds
  | m == 0  = validate ds (build Va n)
  | m == n  = validate ds (build Oc n)
    where n = length ds
-- for complex situation, generate a list, validate them, then evidence them.
applyRule seq ds
  | sum seq + length seq - 1 <= n = foldl evidenceM Nothing (map (validate ds) (generate n seq))
  | otherwise = Nothing
    where n = length ds

-- partialFill take a state, and produce a list of [Disc] gauss
-- Notice that if one of the (Maybe [Disc]) is Nothing, 
--   the whole (Maybe [[Disc]]) will be Nothing.
partialFill :: ([Sequence], [[Disc]]) -> Maybe [[Disc]]
partialFill = sequence . (uncurry . zipWith $ applyRule)

partialFillM :: ([Sequence], Maybe [[Disc]]) -> Maybe [[Disc]]
partialFillM =  undefined

-- reduceState map a state to another inferred state, it use partialFill method,
-- Notice that if one of the (Maybe [Disc]) from partialFill is Nothing,
--   the whole (Maybe [[Disc]]) will be Nothing.
reduceState :: ([Sequence], [[Disc]]) -> ([Sequence], Maybe [[Disc]])
reduceState x = ((fst x), id (partialFill x))


within                    :: (t -> Bool) -> [t] -> t
within tolfunc (x:xs)
  | tolfunc x             = x
  | otherwise             = within tolfunc xs

solveNew                  :: [[Sequence]] -> Maybe [[Disc]]
solveNew [hs, vs]         =  solvePartial [hs, vs] $ createDisc (length hs) (length vs)

solvePartial              :: [[Sequence]] -> [[Disc]] -> Maybe [[Disc]]
solvePartial [hs, vs] dss =  snd $ 
                             within (\(seqs, mdss) -> hs == seqs 
                                    && case mdss of Nothing -> True
                                                    (Just dss) -> uncertainty dss == 0)
                                    (stream (cycle [hs, vs]) (hs, Just dss))

goalCheck                         :: [Sequence] -> ([Sequence], Maybe [[Disc]]) -> Bool
goalCheck targetSeqs (seqs, mdss) = seqs == targetSeqs 
                                    && case mdss of Nothing -> True
                                                    (Just dss) -> uncertainty dss == 0

--stream
stream :: [[Sequence]] -> ([Sequence], Maybe [[Disc]]) -> [([Sequence], Maybe [[Disc]])]
stream cseqss x@(seqs, Nothing)  = x:[]
stream cseqss x@(seqs, Just dss) = x:(stream (tail cseqss) 
                                              ((head cseqss), 
                                                partialFill ((head cseqss), transpose dss) ) )
{-
stream :: [[Sequence]] -> Maybe [[Disc]] -> [Maybe [[Disc]]]
stream cseqss mdss@(Nothing)  = mdss:[]
stream cseqss mdss@(Just dss) = mdss:(stream (tail cseqss) 
                                             (partialFill ((head cseqss), transpose dss) ) )-}


solve :: [([Sequence], Maybe [[Disc]])] -> Maybe [[Disc]]
solve [(_,Nothing),_] = Nothing
solve [_,(_,Nothing)] = Nothing
solve [(hr,Just g),(vr,gt)]
  | uncertainty g == 0 = Just g
  | otherwise          = solve $ [(vr, transform . snd $ result), result] 
                            where result = reduceState (hr,g)


