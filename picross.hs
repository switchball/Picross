import Data.List (transpose, intersperse, intercalate)
import Control.Monad
import Data.Time (getCurrentTime, diffUTCTime, NominalDiffTime)

count x xs = length $ filter (==x) xs

counti x xs = length $ filter (/=x) xs

count2d x xss = sum $ map (count x) xss

-- build a 2d-list with ns seperate element x
-- build x [1,0,2] = [[x],[],[x,x]]
buildseq      :: a -> [Int] -> [[a]]
buildseq x ns = map (\n -> replicate n x) ns


data Disc = Un|Oc|Va
            deriving (Read,Eq)

instance Show Disc where
  show Un = "?"
  show Oc = "o"
  show Va = "."

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

discXor :: Disc -> Disc -> Flag
discXor Un Un = False
discXor Va Va = False
discXor Oc Oc = False
discXor _  _  = True

createDisc :: Int -> Int -> [[Disc]]
createDisc m = replicate m . createDisc1d

createDisc1d :: Int -> [Disc]
createDisc1d n = replicate n Un

createSeq :: [Int] -> Sequence
createSeq =  id

createSeqs :: [[Int]] -> [Sequence]
createSeqs =  id

type Sequence = [Int]
type Sequences = [[Int]]

type Flag = Bool



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
-- =================================
-- ..O...O.O.O..O..O.....
--   |   | | |  |  |
--   0   1 2 3 ... m        => m=5
-- xx xxx x x xx xx xxxxx   => n=16
-- ()               (---)   => (---) can be zero length
-- =================================
-- The number of solutions is C(n+1, m). (n+1>=m)
-- Note: n>=m-1 should be true, otherwise there is no solutions.
intpartition     :: Int -> Int -> [[Int]]
intpartition n 0 = [[n]]
intpartition n m = concatMap (\k -> map (k:) (mintpat0 (n-k) m) ) [0..(n-m+1)]

-- =========================
-- ..O...O.O.O..O..O
--   |   | | |  |  |
--   0   1 2 3 ... m => m=5
--    xxx x x xx xx  => n=9
-- =========================
-- minpat is meant to find m integers with sum=n, list all combinations.
-- illustrated above.
-- The number of solutions is C(n-1, m-1). (n>=m)
-- Note: n>=m should be true, otherwise there is no solutions.
mintpat :: Int -> Int -> [[Int]]
mintpat n m 
  | n > 0  && m == 0 = []
  | n == 0 && m == 0 = [[]]
  | n >= 1 && m == 1 = [[n]]
  | n < m            = []
  | otherwise        = concatMap (\k -> map (k:) (mintpat (n-k) (m-1))) [1..(n-m+1)]

-- =================================
-- ..O...O.O.O..O..O.....
--   |   | | |  |  |     |
--   0   1 2 3 ... m-1   m  => m=6
--    xxx x x xx xx xxxxx   => n=14
--                  (---)   => (---) can be zero length
-- =================================
-- The difference between mintpat and mintpat0, 
-- is mintpat0 can have the last element to be zero.
-- each solution contains m integers, with sum=n.
-- The number of solutions is C(n, m-1). (n>=m-1)
-- Note: n>=m-1 should be true, otherwise there is no solutions.
mintpat0 :: Int -> Int -> [[Int]]
mintpat0 n m 
  | n > 0  && m == 0 = []
  | n == 0 && m == 0 = [[]]
  | n >= 0 && m == 1 = [[n]]
  | n < m - 1        = []
  | otherwise        = concatMap (\k -> map (k:) (mintpat0 (n-k) (m-1))) [1..(n-m+2)]

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
applyRule []  ds = validate ds (replicate n Va) where n = length ds
applyRule [m] ds
  | m == 0  = validate ds (replicate n Va)
  | m == n  = validate ds (replicate n Oc)
    where n = length ds
applyRule seq ds
-- check the uncertainty of ds first
  | count Un ds == 0              = Just ds
-- for complex situation, generate a list, validate them, then evidence them.
  | sum seq + length seq - 1 <= n = foldl evidenceM Nothing (map (validate ds) (generate n seq))
  | otherwise = Nothing
    where n = length ds


within                    :: Int -> (t -> Bool) -> [t] -> t
within maxiter tolfunc (x:xs)
  | maxiter == 0          = x
  | tolfunc x             = x
  | otherwise             = within (maxiter-1) tolfunc xs

-- cutdown a stream, act like takeWhile
cutdown                   :: Int -> (t -> Bool) -> [t] -> [t]
cutdown _  _  []          =  []
cutdown maxiter tolfunc (x:xs)
  | maxiter == 0          =  [x]
  | tolfunc x             =  [x]
  | otherwise             =  x:(cutdown (maxiter-1) tolfunc xs)

fastcheck                 :: [[Sequence]] -> Int
fastcheck [hs, vs]        =  sum (concat hs) - sum (concat vs) 

solveNew                  :: [[Sequence]] -> Maybe [[Disc]]
solveNew [hs, vs]         =  solvePartial [hs, vs] $ createDisc (length hs) (length vs)

solvePartial              :: [[Sequence]] -> [[Disc]] -> Maybe [[Disc]]
solvePartial [hs, vs] dss =  snd $ within 100 (goalCheck hs)
                                          (stream (cycle [hs, vs]) (hs, Just (transpose dss)))

goalCheck                         :: [Sequence] -> ([Sequence], Maybe [[Disc]]) -> Bool
goalCheck targetSeqs (seqs, mdss) = seqs == targetSeqs 
                                    && case mdss of Nothing -> True
                                                    (Just dss) -> uncertainty dss == 0

-- fillWithFlags take a flag list, a state, and produce a list of [Disc] guess
-- length of [Flag], [Sequence], [[Disc]] should be equal.
-- Notice that if one of the (Maybe [Disc]) is Nothing, 
--   the whole (Maybe [[Disc]]) will be Nothing.
fillWithFlags :: [Flag] -> [Sequence] -> [[Disc]] -> Maybe [[Disc]]
fillWithFlags fs qs dss = sequence (zipWith3 
                            (\f q ds -> if f then (applyRule q ds) else (Just ds))
                             fs qs dss)
                          where -- Note: small heuristic value does not mean easy to calculate
                            n         = length (dss!!0)
                            heuristic = zipWith3 (\f q ds->if f then (n-sum q)^(length q)`div`(1+counti Un ds) else 0) fs qs dss
                            inf       = foldl min (2^31) (filter (>0) heuristic)
                            sup       = inf * 100
                            filtered  = map (\x-> x<=sup) heuristic
                            chosen    = zipWith (||) fs filtered


-- generate a stream containing main state of current [[Disc]],
-- the stream maybe finite (in this case Nothing is the last element),
-- or maybe infinite (can both be solved or have some uncertain structure).
-- it feeds the within method.
stream :: [[Sequence]] -> ([Sequence], Maybe [[Disc]]) -> [([Sequence], Maybe [[Disc]])]
stream cseqss ins = map (snd.snd) (instream cseqss (0, (flag0, ins)))
                    where flag0 = (replicate (length (fst ins)) True)

-- inner stream have more inner temp state which the outside world does not need to know,
-- it is the more general version than stream.
-- The Flag is to indicate which column is changed.
-- The Int  is to indicate which loop it is.
-- The init value's Int is 0, when it is 0 or 1, flag must be all set to True,
-- This avoid a infinite loop bug when first (hor) infer failed.
instream :: [[Sequence]] -> (Int, ([Flag], ([Sequence], Maybe [[Disc]]))) -> [(Int, ([Flag], ([Sequence], Maybe [[Disc]])))]
instream cseqss x@(loop, (flags, (seqs, Nothing)))  = x:[]
instream cseqss x@(loop, (flags, (seqs, Just dss))) = 
  x:(instream (tail cseqss) 
              (loop+1, (newflags,   ( hseqs, result ) ) ) )
  where hseqs  = head cseqss
        result = fillWithFlags flags hseqs (transpose dss)
        newflags = if loop == 0 then (replicate (length (head (tail cseqss))) True) else
                   case result of (Just newdiscss) -> diffHor dss (transpose newdiscss)
                                  otherwise -> (replicate 25 False)
{-
stream :: [[Sequence]] -> Maybe [[Disc]] -> [Maybe [[Disc]]]
stream cseqss mdss@(Nothing)  = mdss:[]
stream cseqss mdss@(Just dss) = mdss:(stream (tail cseqss) 
                                             (partialFill ((head cseqss), transpose dss) ) )-}

diff :: [[Disc]] -> [[Disc]] -> [[Flag]]
diff =  zipWith (zipWith discXor)

diffHor :: [[Disc]] -> [[Disc]] -> [Flag]
diffHor x y = map or (diff x y)

diffVer :: [[Disc]] -> [[Disc]] -> [Flag]
diffVer x y = map or (transpose (diff x y))

timing :: [[Sequence]] -> IO NominalDiffTime
timing [hs,vs] = do start <- getCurrentTime
                    putStrLn $ show $ Graph $ solveNew [hs,vs]
                    stop  <- getCurrentTime
                    return $ diffUTCTime stop start

trace :: [[Sequence]] -> IO ()
trace [hs, vs] = do
    putInStreams (cutdown 49 ((goalCheck hs).snd.snd) state)
    where state = instream (cycle [hs, vs]) (0, (flag0, (hs, Just (transpose dss))))
          dss   = createDisc (length hs) (length vs)
          flag0 = (replicate (length hs) True)

putInStreams :: [(Int, ([Flag], ([Sequence], Maybe [[Disc]])))] -> IO ()
putInStreams [] = putStrLn "[END]"
putInStreams (insm:insms) = 
  do putStrLn ("loop [#" ++ (show loopid) ++ "]")
     putStrLn ("< " ++ (showFlags flags))
     putDisc  graph
     putInStreams insms
     where loopid = fst insm
           flags  = (fst.snd) insm
           seqs   = (fst.snd.snd) insm
           graph  = (snd.snd.snd) insm
           showFlags :: [Flag] -> String
           showFlags []     = ">"
           showFlags (f:fs) = (if f then "T " else "F ") ++ (showFlags fs)


putStreams :: [([Sequence], Maybe [[Disc]])] -> IO ()
putStreams [] = putStrLn "[END]"
putStreams (stream:streams) = do putStrLn (show (fst stream))
                                 putDisc (snd stream)
                                 putStreams streams

putDisc :: Maybe [[Disc]] -> IO ()
putDisc dss = do putStrLn (show (Graph dss))

data Graph = Graph (Maybe [[Disc]])

instance Show Graph where
  show (Graph Nothing)         = "NOTHING"
  show (Graph (Just[]))        = ""
  show (Graph (Just (ds:dss))) = "| " ++ line ds ++ "|\n" ++ show (Graph (Just dss))
    where line [] = ""
          line (d:ds) = show (d) ++ " " ++ line (ds)

seq0   = createSeq [0]
seq3   = createSeq [3]
seq5   = createSeq [5]
seq12  = createSeq [1,2]
seq111 = createSeq [1,1,1]

disc1d = createDisc1d 5
disc2d = createDisc 3 3


discSmall  = createDisc 5 5
discMedium = createDisc 10 10
discLarge  = createDisc 15 15
-- == Test Case == --
{- Case No.1 Sprite [0.01s]
| . o o o . |
| o . o . o |
| o o o o o |
| . o o o . |
| . o . o . |
-}
seqsHor1 = createSeqs [[3],[1,1,1],[5],[3],[1,1]]
seqsVer1 = createSeqs [[2],[1,3],[4],[1,3],[2]]
p1       = [seqsHor1,seqsVer1]
discCor1 = [[Va,Oc,Oc,Oc,Va],
            [Oc,Va,Oc,Va,Oc],
            [Oc,Oc,Oc,Oc,Oc],
            [Va,Oc,Oc,Oc,Va],
            [Va,Oc,Va,Oc,Va]]

{- Case No.2 Snow [0.01s]
| . . o . . |
| o o . o o |
| . o . o . |
| o o . o o |
| . . o . . |
-}
seqsHor2 = createSeqs [[1],[2,2],[1,1],[2,2],[1]]
seqsVer2 = createSeqs [[1,1],[3],[1,1],[3],[1,1]]
p2       = [seqsHor2,seqsVer2]
discCor2 = [[Va,Va,Oc,Va,Va],
            [Oc,Oc,Va,Oc,Oc],
            [Va,Oc,Va,Oc,Va],
            [Oc,Oc,Va,Oc,Oc],
            [Va,Va,Oc,Va,Va]]

{- Case No.3 Box [0.05s]
| o o o o o o o o o o |
| o . . . . . . . . o |
| o . . . . . . . . o |
| o . . . o o . . . o |
| o . . . o o . . . o |
| o . . . o o . . . o |
| o . . . o o . . . o |
| o . . . . . . . . o |
| o . . . . . . . . o |
| o o o o o o o o o o |
-}
seqsHor3 = createSeqs [[10],[1,1],[1,1],[1,2,1],[1,2,1],[1,2,1],[1,2,1],[1,1],[1,1],[10]]
seqsVer3 = createSeqs [[10],[1,1],[1,1],[1,1],[1,4,1],[1,4,1],[1,1],[1,1],[1,1],[10]]
p3       = [seqsHor3,seqsVer3]
discCor3 = undefined

{- Case No.4 Unknown [0.06s]
| . . . . . . . . . . |
| ? o o ? . . . . . o |
| ? o o ? . . . o o o |
| . . o o o o o o o o |
| o o o o o o o o o o |
| o o o o o o o o o o |
| . . o o o o o o o o |
| ? o o ? . . . o o o |
| ? o o ? . . . . . o |
| . . . . . . . . . . |
-}
seqsHor4 = createSeqs [[1,2,1],[2,2,2],[8],[6],[4],[4],[4],[6],[6],[8]]
seqsVer4 = createSeqs [[0],[3,1],[3,3],[8],[10],[10],[8],[3,3],[3,1],[0]]
p4       = [seqsHor4,seqsVer4]
discCor4 = undefined

{- Case No.5 Heart [0.08s]
| . . o o o . . . . . o o o . . |
| . o o o o o . . . o o . o o . |
| . o o o o o o . o o o o . o . |
| o o o o o o o o o o o o o o o |
| o o . o o . o . o o . o . o o |
| o o . o . . . . . o . o . o o |
| . o . o o . . . o o . o . o . |
| . o . o o o . o o o . . . o . |
| . . o o o o o o o o o o o . . |
| . . . o o o o o o o o o . . . |
| . . . . o o o o o o o . . . . |
| . . . . . o o o o o . . . . . |
| . . . . . . o o o . . . . . . |
| . . . . . . . o . . . . . . . |
-}
seqsHor5 = createSeqs [[3,3],[5,2,2],[6,4,1],[15],[2,2,1,2,1,2],[2,1,1,1,2],
                       [1,2,2,1,1],[1,3,3,1],[11],[9],[7],[5],[3],[1]]
seqsVer5 = createSeqs [[3],[7],[4,1],[10],[5,5],[3,5],[3,5],[1,7],[3,7],[11],
                       [4,3],[1,5,2],[2,1,1],[7],[3]]
p5       = [seqsHor5,seqsVer5]
disc5    = createDisc 14 15
discCor5 = undefined


{- Case No.6 [0.11s]
| o o o o o o o o o o o o o o o |
| o . . o . o . . . o . o . . o |
| o . . o o o . . . o o o . . o |
| o o o o . o . . . o . o o o o |
| o . o . o o o o o o o . o . o |
| o o o o o . . . . . o o o o o |
| o . . . o . o o o . o . . . o |
| o . . . o . o . o . o . . . o |
| o . . . o . o o o . o . . . o |
| o o o o o . . . . . o o o o o |
| o . o . o o o o o o o . o . o |
| o o o o . o . . . o . o o o o |
| o . . o o o . . . o o o . . o |
| o . . o . o . . . o . o . . o |
| o o o o o o o o o o o o o o o |
-}
seqsHor6 = createSeqs [[15],[1,1,1,1,1,1],[1,3,3,1],[4,1,1,4],[1,1,7,1,1],[5,5],
                       [1,1,3,1,1],[1,1,1,1,1,1],[1,1,3,1,1],[5,5],[1,1,7,1,1],
                       [4,1,1,4],[1,3,3,1],[1,1,1,1,1,1],[15]]
seqsVer6 = seqsHor6
p6       = [seqsHor6,seqsVer6]
discCor6 = undefined


{- Case No.7 Superman [0.04s]
| . o o o o o o o o . |
| o o o . . . . o o o |
| o o . o o o o . o o |
| o o . o o o o o o o |
| o o o . . . o o o o |
| . o o o o o . o o . |
| . o o . o o . o o . |
| . . o o . . o o . . |
| . . o o o o o o . . |
| . . . o o o o . . . |
-}
seqsHor7 = createSeqs [[8],[3,3],[2,4,2],[2,7],[3,4],[5,2],[2,2,2],[2,2],[6],[4]]
seqsVer7 = createSeqs [[4],[7],[2,5],[1,2,1,3],[1,2,2,2],[1,2,2,2],[1,3,3],[2,6],[7],[4]]
p7       = [seqsHor7,seqsVer7]
discCor7 = undefined

{- Case No.8 Detective [0.12s]
| . . . . . o o o o o . . . . . |
| . . . o o o . . . o o o . . . |
| . . . . o o o o o o o . . . . |
| . . . . o o o . o o o . . . . |
| . . . . o . . . . . o . . . . |
| . . . . o . . o . . o . . . . |
| . . o o o o . . . o o o o . . |
| . o o . . o o . o o . . o o . |
| o o o . o o o . o o o . o o o |
| o o . . o . o . o . o . o o o |
| o o . o o . o o o . o . o o . |
| . o . o o . o . o . o o o . . |
| . o o o o o o . o o o o . . . |
| . . o o . o . . . o . o o . . |
| . o o o o o . . . o o o o o . |
-}
seqsHor8 = createSeqs [[5],[3,3],[7],[3,3],[1,1],[1,1,1],[4,4],[2,2,2,2],[3,3,3,3],
                       [2,1,1,1,1,3],[2,2,3,1,2],[1,2,1,1,3],[6,4],[2,1,1,2],[5,5]]
seqsVer8 = createSeqs [[3],[6,1],[3,3],[1,1,5],[6,5,1],[4,3,3],[1,2,6],[1,1,1,1],
                       [1,2,6],[4,3,3],[6,5,1],[1,1,4],[6,2],[4,1],[2]]
p8       = [seqsHor8,seqsVer8]
discCor8 = undefined


{- Case No.9 Squirrel [0.06s]
| . . . . . . o . . . o o o o . |
| . . o o o o o . . o o . . o o |
| . o o o o o . . o o o . o o o |
| o o o . o o . . o o . o . . o |
| o o o o o o . . o o . o . o o |
| . o o o o o o . o o o . o o o |
| . . . o o o o . o o o . o o o |
| . . o o . o o o o o o o o . o |
| . o o . o o o o o o o o o . o |
| . . . o o o o o o o o o . o . |
| . . o o o o o o o o o o . o . |
| . . o o o o o o o o o . o . . |
| . . . o . o o o o . . o . . . |
| . . . . o . o o o o o . . . . |
| . . . o o o o o o . . . . . . |
-}
seqsHor9 = createSeqs [[1,4],[5,2,2],[5,3,3],[3,2,2,1,1],[6,2,1,2],[6,3,3],[4,3,3],
                       [2,8,1],[2,9,1],[9,1],[10,1],[9,1],[1,4,1],[1,5],[6]]
seqsVer9 = createSeqs [[2],[4,1],[5,2,2],[2,4,4,1],[6,4,2],[12,1],[2,10],[8],[13],
                       [11,1],[3,7,1],[1,2,4,1],[1,1,4,1],[3,3,2],[8]]
p9       = [seqsHor9,seqsVer9]
discCor9 = undefined


{- Case No.10 Where's my Home? [1.09s]
| o . . o . . . . o . . o o o . . . . . . |
| o . . o . . . o o . o o o . . . . . . . |
| o . . o . . . o o . o o . . . . . . . . |
| o o . o . . . o o o o . . . . . . . . . |
| o o . o o . o o o o . . . . . . . . . . |
| o o . . o o o o . . . . o o o o . . . . |
| o o o . . o o o . . . o o . . . . . . . |
| . o o . . o o . . o o o . . . . . . . . |
| o . o o . o o . o o . . . . . . . . . . |
| o o o o o o o o o . . . . . . . . . . . |
| o o o o o o o . . . . . . . o o . . . . |
| o o o o o o . . . . . . o o . o o . . . |
| o o o o o . . . . . . . . o o o o . . . |
| o o o o o . . . . . . . . . o o . . . . |
| o . o o o . . . . . . . . . o o o . . . |
| o . o o o . . . . . . . . . o o o o . . |
| o . o o o . . . . . . . . . o o o o o o |
| o o o o o . . . . . . . . . . o o o o . |
| o o o o o . . . . . . . . . . . o . . . |
| o o o o o . . . . . . . . . . o o . . . |
-}
seqsHor10 = createSeqs [[1,1,1,3],[1,1,2,3],[1,1,2,2],[2,1,4],[2,2,4],[2,4,4],
                        [3,3,2],[2,2,3],[1,2,2,2],[9],[7,2],[6,2,2],[5,4],[5,2],
                        [1,3,3],[1,3,4],[1,3,6],[5,4],[5,1],[5,2]]
seqsVer10 = createSeqs [[7,12],[5,5,3],[14],[5,12],[2,11],[7],[7],[6,1],[5,2],
                        [2,2],[3,1],[3,2],[2,2,1],[1,1,2],[1,1,5],[1,8,1],[2,6],[3],[2],[1]]
p10       = [seqsHor10,seqsVer10]
discCor10 = undefined


{- Case No.11 Apple [0.34s]
| . . . . . . . . . o . . . . . . . . . . |
| . . . . o o o o . o . . o o o o o . . . |
| . . . o o o o o o o . o o o o o o o . . |
| . . o o o o o . . o o . o o o o o o o . |
| . o . . . . . . . o . . . . . . . . . o |
| . . . o o o o o . o . o o o o o . . . . |
| . . o o o . o o o o o o o o o o o . . . |
| . o o . . o o o o o o o o o o o o o . . |
| . o . . o o o o o o o o o o o o o o . . |
| o o . . o o o o o o o o o o o o o o o . |
| o o . . o o o o o o o o o o o . o o o . |
| o o . . o o o o o o o o o o o o . o o . |
| o o . . o o o o o o o o o o o o . o o . |
| o o . . o o o o o o o o o o o o . o o . |
| . o . . o o o o o o o o o o o o . o . . |
| . o o . . o o o o o o o o o o . o o . . |
| . . o o . . o o o o o o o o . o o . . . |
| . . . o o o . o o o o o o o o o . . . . |
| . . . . o o o o o o o o o o o . . . . . |
| . . . . . o o o . o o . o o . . . . . . |
-}
seqsHor11 = createSeqs [[1],[4,1,5],[7,7],[5,2,7],[1,1,1],[5,1,5],[3,11],[2,13],
                        [1,14],[2,15],[2,11,3],[2,12,2],[2,12,2],[2,12,2],[1,12,1],
                        [2,10,2],[2,8,2],[3,9],[11],[3,2,2]]
seqsVer11 = createSeqs [[5],[1,9],[1,2,2],[2,2,2],[3,2,7,2],[3,1,9,3],[3,12,2],[2,15],
                        [1,13],[20],[1,14],[1,14],[3,15],[3,15],[3,11,2],[3,5,4,2],
                        [3,5,2],[2,9],[1,5],[1]]
p11       = [seqsHor11,seqsVer11]
discCor11 = undefined

{- Case No.12 Rabbit on Acid [7.84s]
| . . . . o o o o o . o o o o o . . . . . |
| . o o o . . . . . o . . . . o o . . . . |
| . o . . . . . . . o o o o o . o o . . . |
| o . . o o o o . . . o o o o o . o . . . |
| o o o o o o o o . . . o o o o . o . . . |
| . . . . . . o o o . . o o o o . o . . . |
| . . . . . . . . o o . . o o o . o . . . |
| . . . . . . . . o o . . o o o . o . . . |
| . . . . . . . . o o o . o o . . o . . . |
| . . . . . . . . o . . . . . . o o . . . |
| . . . . . . . o o o o o o o . . o . . . |
| . . . . . . o . . . o . . . o . o o . . |
| . . . . . . o . o . o . o . o . . o . . |
| . . o . . o o . . . o . . . . o . o . . |
| . . . . o o . o o o o o o o o . . . o . |
| . o o o o . . o o o o . . . o . o o o o |
| . . . o . . o . . o . . o . . . . . o . |
| . . o o o . . . o o o . . . o . . o o o |
| . o . . o o . o . o . o . . . . o o . . |
| . . . o . o o o . o . o o o o o o . o . |
-}
seqsHor12 = createSeqs [[5,5],[3,1,2],[1,5,2],[1,4,5,1],[8,4,1],[3,4,1],[2,3,1],[2,3,1],
                        [3,2,1],[1,2],[7,1],[1,1,1,2],[1,1,1,1,1,1],[1,2,1,1,1],[2,8,1],
                        [4,4,1,4],[1,1,1,1,1],[3,3,1,3],[1,2,1,1,1,2],[1,3,1,6,1]]
seqsVer12 = createSeqs [[2],[2,1,1,1],[1,1,1,1,1],[1,2,3,1],[1,2,2,2],[1,2,2,2],[1,3,3,1,1],
                        [1,2,1,2,2],[1,6,1,2,1],[2,3,1,6],[1,2,1,6,1],[1,4,1,1,2],
                        [1,7,1,1,1,1,1],[1,7,1,1,1],[2,5,2,2,1,1],[2,1,1,1],[10,1,2],
                        [3,1,2],[4,1],[1,1]]
p12       = [seqsHor12,seqsVer12]
discCor12 = undefined

{- Case No.13 Multi-solve chain
| ? o ? . . |
| o . o . . |
| ? o o o ? |
|   . o . o |
| . . ? o ? |
-}
seqsHor13 = createSeqs [[2],[1,1],[4],[1,1],[2]]
seqsVer13 = createSeqs [[2],[1,1],[4],[1,1],[2]]
p13       = [seqsHor13,seqsVer13]
discCor13 = undefined

{- Case No.14 QR Code [4.99s]
  [Incomplete version]
-}
seqsHor14 = createSeqs 
  [[7,1,2,7],[1,1,2,1,1,1],[1,3,1,2,1,1,3,1],[1,3,1,1,1,1,3,1],[1,3,1,1,1,1,3,1],[1,1,1,2,1,1],
   [7,1,1,1,7],[5],[2,1,2,2,3,2],[1,1,1,2,4],[2,3,2,2,1],[1,1,1,1,2,2,2],[1,1,1,1,1,1,1,1],
   [4,1,1],[7,1,1,2,1],[1,1,4,1,1],[1,3,1,2,1,1,1],[1,3,1,4,1,2],[1,3,1,1,1,2,1],[1,1,1,2],
   [7,1,3,1,1,1]]
seqsVer14 = createSeqs 
  [[7,1,2,7],[1,1,1,1,1,1,1],[1,3,1,1,1,1,3,1],[1,3,1,1,1,3,1],[1,3,1,2,1,3,1],[1,1,2,1,1],
   [7,1,1,1,7],[1,2],[2,4,3,1,2],[4,2,1,2],[4,1,1,3,1],[2,1,1,1,1,1,3,1],[1,1,4,1,1,1,1,1],
   [1,2,1],[7,2,1,1,1],[1,1,2,1,1,1],[1,3,1,1,2,2,2],[1,3,1,3,1,1,1],[1,3,1,3],[1,1,2,1,2,1,1],
   [7,4,4]]
p14       = [seqsHor14,seqsVer14]
discCor14 = undefined