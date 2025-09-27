{-
   DomsMatch: code to play a dominoes match between two players.

   The top level function is domsMatch - it takes five arguments:
       games - the number of games to play
       target - the target score to reach
       player1, player2 - two DomsPlayer functions, representing the two players
       seed - an integer to seed the random number generator
   The function returns a pair showing how many games were won by each player.

   The functions of type DomsPlayer must take four arguments:
       The current Hand
       The current Board
       The Player (which will be one of P1 or P2)
       The current Scores
   The function returns a tuple containing the Domino to play and End to play it on.

   Stub with types provided by Emma Norling (October 2023).

   You should add your functions and any additional types that you require to your own copy of
   this file. Before you submit, make sure you update this header documentation to remove these
   instructions and replace them with authorship details and a brief summary of the file contents.

   Similarly, remember you will be assessed not *just* on correctness, but also code style,
   including (but not limited to) sensible naming, good functional decomposition, good layout,
   and good comments.
 -}

module DomsMatch where

import Data.List
import Data.Ord (comparing)

import System.Random

-- types used in this module
type Domino = (Int, Int) -- a single domino
{- Board data type: either an empty board (InitState) or the current state as represented by
    * the left-most domino (such that in the tuple (x,y), x represents the left-most pips)
    * the right-most domino (such that in the tuple (x,y), y represents the right-most pips)
    * the history of moves in the round so far
 -}

data Board = InitState | State Domino Domino History deriving (Eq, Show)

{- History should contain the *full* list of dominos played so far, from leftmost to
   rightmost, together with which player played that move and when they played it
 -}
type History = [(Domino, Player, MoveNum)]

data Player = P1 | P2 deriving (Eq, Show)

data End = L | R deriving (Eq, Show)

type Scores = (Int, Int) -- P1’s score, P2’s score

type MoveNum = Int

type Hand = [Domino]

{- DomsPlayer is a function that given a Hand, Board, Player and Scores will decide
   which domino to play where. The Player information can be used to "remember" which
   moves in the History of the Board were played by self and which by opponent
 -}
type DomsPlayer = Hand -> Board -> Player -> Scores -> (Domino, End)

{- domSet: a full set of dominoes, unshuffled -}
domSet = [(l, r) | l <- [0 .. 6], r <- [0 .. l]]

{- shuffleDoms: returns a shuffled set of dominoes, given a number generator
   It works by generating a random list of numbers, zipping this list together
   with the ordered set of dominos, sorting the resulting pairs based on the random
   numbers that were generated, then outputting the dominos from the resulting list.
 -}
shuffleDoms :: StdGen -> [Domino]
shuffleDoms gen = [d | (r, d) <- sort (zip (randoms gen :: [Int]) domSet)]

{- domsMatch: play a match of n games between two players,
    given a seed for the random number generator
   input: number of games to play, number of dominos in hand at start of each game,
          target score for each game, functions to determine the next move for each
          of the players, seed for random number generator
   output: a pair of integers, indicating the number of games won by each player
 -}
domsMatch :: Int -> Int -> Int -> DomsPlayer -> DomsPlayer -> Int -> (Int, Int)
domsMatch games handSize target p1 p2 seed =
  domsGames games p1 p2 (mkStdGen seed) (0, 0)
  where
    domsGames 0 _ _ _ wins = wins
    domsGames n p1 p2 gen (p1_wins, p2_wins) =
      domsGames (n - 1) p1 p2 gen2 updatedScore
      where
        updatedScore
          | playGame handSize target p1 p2 (if odd n then P1 else P2) gen1 == P1 = (p1_wins + 1, p2_wins)
          | otherwise = (p1_wins, p2_wins + 1)
        (gen1, gen2) = split gen

{- Note: the line above is how you split a single generator to get two generators.
   Each generator will produce a different set of pseudo-random numbers, but a given
   seed will always produce the same sets of random numbers.
 -}

{- playGame: play a single game (where winner is determined by a player reaching
      target exactly) between two players
   input: functions to determine the next move for each of the players, player to have
          first go, random number generator
   output: the winning player
 -}
playGame :: Int -> Int -> DomsPlayer -> DomsPlayer -> Player -> StdGen -> Player
playGame handSize target p1 p2 firstPlayer gen =
  playGame' p1 p2 firstPlayer gen (0, 0)
  where
    playGame' p1 p2 firstPlayer gen (s1, s2)
      | s1 == target = P1
      | s2 == target = P2
      | otherwise =
          let newScores = playDomsRound handSize target p1 p2 firstPlayer currentG (s1, s2)
              (currentG, nextG) = split gen
           in playGame' p1 p2 (if firstPlayer == P1 then P2 else P1) nextG newScores

{- playDomsRound: given the starting hand size, two dominos players, the player to go first,
    the score at the start of the round, and the random number generator, returns the score at
    the end of the round.
    To complete a round, turns are played until either one player reaches the target or both
    players are blocked.
 -}
playDomsRound :: Int -> Int -> DomsPlayer -> DomsPlayer -> Player -> StdGen -> (Int, Int) -> (Int, Int)
playDomsRound handSize target p1 p2 first gen scores =
  playDomsRound' p1 p2 first (hand1, hand2, InitState, scores)
  where
    -- shuffle the dominoes and generate the initial hands
    shuffled = shuffleDoms gen
    hand1 = take handSize shuffled
    hand2 = take handSize (drop handSize shuffled)
    {- playDomsRound' recursively alternates between each player, keeping track of the game state
       (each player's hand, the board, the scores) until both players are blocked -}
    playDomsRound' p1 p2 turn gameState@(hand1, hand2, board, (score1, score2))
      | (score1 == target) || (score2 == target) || (p1_blocked && p2_blocked) = (score1, score2)
      | turn == P1 && p1_blocked = playDomsRound' p1 p2 P2 gameState
      | turn == P2 && p2_blocked = playDomsRound' p1 p2 P1 gameState
      | turn == P1 = playDomsRound' p1 p2 P2 newGameState
      | otherwise = playDomsRound' p1 p2 P1 newGameState
      where
        p1_blocked = blocked hand1 board
        p2_blocked = blocked hand2 board
        (domino, end) -- get next move from appropriate player
          | turn == P1 = p1 hand1 board turn (score1, score2)
          | turn == P2 = p2 hand2 board turn (score1, score2)
        -- attempt to play this move
        maybeBoard -- try to play domino at end as returned by the player
          | turn == P1 && not (domInHand domino hand1) = Nothing -- can't play a domino you don't have!
          | turn == P2 && not (domInHand domino hand2) = Nothing
          | otherwise = playDom turn domino board end
        newGameState -- if successful update board state (exit with error otherwise)
          | maybeBoard == Nothing = error ("Player " ++ show turn ++ " attempted to play an invalid move.")
          | otherwise =
              ( newHand1,
                newHand2,
                newBoard,
                (limitScore score1 newScore1, limitScore score2 newScore2)
              )
        (newHand1, newHand2) -- remove the domino that was just played
          | turn == P1 = (hand1 \\ [domino], hand2)
          | turn == P2 = (hand1, hand2 \\ [domino])
        score = scoreBoard newBoard (newHand1 == [] || newHand2 == [])
        (newScore1, newScore2) -- work out updated scores
          | turn == P1 = (score1 + score, score2)
          | otherwise = (score1, score2 + score)
        limitScore old new -- make sure new score doesn't exceed target
          | new > target = old
          | otherwise = new
        Just newBoard = maybeBoard -- extract the new board from the Maybe type

{- domInHand: check if a particular domino is contained within a hand -}
domInHand :: Domino -> Hand -> Bool
domInHand (l, r) hand = [1 | (dl, dr) <- hand, (dl == l && dr == r) || (dr == l && dl == r)] /= []



scoreBoard :: Board -> Bool -> Int
scoreBoard InitState _ = 0 -- no dominos played would result in score 0
scoreBoard (State (x1, y1) (x2, y2) history) isLastDomino
  | isLastDomino = calculateScore x1 y2 + 1 -- Add 1 to the score if it is the last domino
  | otherwise = calculateScore x1 y2
  where
    -- | 'calculateScore' calculates the score based on the pips of the last domino.
    calculateScore :: Int -> Int -> Int
    calculateScore a b
      | total `mod` 15 == 0 = total `div` 5 + total `div` 3
      | total `mod` 5 == 0 = total `div` 5
      | total `mod` 3 == 0 = total `div` 3
      | otherwise = 0 -- No additional points for other cases
      where
        total = a + b -- Sum of pips of the last domino




blocked :: Hand -> Board -> Bool
blocked _ InitState = False -- An empty board can't block a hand
blocked hand board@(State leftDomino rightDomino _) =
  not $ any (\domino -> canPlayAtEnd domino board L || canPlayAtEnd domino board R) hand
-- A player is blocked if none of their dominos can be played on either end of the board.


playDom :: Player -> Domino -> Board -> End -> Maybe Board
playDom player (x, y) InitState end = Just $ State (x, y) (x, y) [((x, y), player, 1)] -- Initial move on an empty board
playDom player (x, y) (State (x1, y1) (x2, y2) history) end
  | end == L = checkCanPlay x1 L -- Check if the move is valid on the left end
  | otherwise = checkCanPlay y2 R -- Check if the move is valid on the right end
  where
    -- | 'checkCanPlay' checks if a move is valid for a given end and updates the board accordingly.
    checkCanPlay :: Int -> End -> Maybe Board
    checkCanPlay z L
      | x == z = Just $ State (y, x) (x2, y2) (((x, y), player, moveNum + 1) : history) -- Play on the left end
      | y == z = Just $ State (x, y) (x2, y2) (((x, y), player, moveNum + 1) : history) -- Play on the left end (reversed)
      | otherwise = Nothing -- Invalid move
    checkCanPlay z R
      | x == z = Just $ State (x1, y1) (x, y) (((x, y), player, moveNum + 1) : history) -- Play on the right end
      | y == z = Just $ State (x1, y1) (y, x) (((x, y), player, moveNum + 1) : history) -- Play on the right end (reversed)
      | otherwise = Nothing -- Invalid move

    -- Get the move number for the current move
    moveNum = case history of
      [] -> 0
      (_, _, lastMoveNum) : _ -> lastMoveNum

played :: Domino -> Board -> Bool
played domino InitState = False -- if the borad is empty no domino has been played yet
played domino (State leftDomino rightDomino history) =
  domInHistory domino history
  where
    -- 'domInHistory' checks if a domino is present in the game history.
    domInHistory :: Domino -> History -> Bool
    domInHistory _ [] = False -- If history is empty, the domino is not present(stoping condtion for the recursion)
    domInHistory domino ((d, _, _) : rest) = domino == d || domInHistory domino rest
    -- Check if the current domino matches the one in the history,
    -- or recursively check the rest of the history.

canPlayAtEnd :: Domino -> Board -> End -> Bool
canPlayAtEnd domino InitState _ = True  -- Any domino can be played on an empty board.

canPlayAtEnd domino (State leftDomino rightDomino history) end
  | end == L = canPlayLeft domino leftDomino  -- Check if the domino can be played on the left.
  | otherwise = canPlayRight domino rightDomino  -- Check if the domino can be played on the right.

  where
    -- Check if the given domino can be played on the left side of the existing domino.
    canPlayLeft :: Domino -> Domino -> Bool
    canPlayLeft (domL, domR) (leftL, leftR) = domR == leftL || domL == leftL

    -- Check if the given domino can be played on the right side of the existing domino.
    canPlayRight :: Domino -> Domino -> Bool
    canPlayRight (domL, domR) (rightL, rightR) = domL == rightR || domR == rightR

possPlays :: Hand -> Board -> ([Domino], [Domino])
possPlays hand board =
  (filter (\domino -> canPlayAtEnd domino board L) hand,  -- Filter dominos playable on the left.
   filter (\domino -> canPlayAtEnd domino board R) hand)  -- Filter dominos playable on the right.

doms2scoreN :: Board -> Int -> [(Domino, End)]
doms2scoreN board n =
  let
    -- Filter out dominos that have already been played on the board.
    unusedDominos = filter (\domino -> not (played domino board)) domSet

    -- Determine possible plays on the left and right ends.
    (leftPlays, rightPlays) = possPlays unusedDominos board
  in
    -- Generate a list of dominos that can achieve the target score on either end.
    [(domino, L) | domino <- leftPlays, maybeScore (playDom P1 domino board L) == n]
    ++ [(domino, R) | domino <- rightPlays, maybeScore (playDom P1 domino board R) == n]
  where
    -- Calculate the score of a given board, considering whether it is the last domino played.
    maybeScore :: Maybe Board -> Int
    maybeScore Nothing = 0
    maybeScore (Just b) = scoreBoard b False



highestScoringPlay :: ([Domino], [Domino]) -> [Domino] -> Board -> Player-> (Domino, End)
highestScoringPlay (leftPlays, rightPlays) hand board player = maximumBy (comparing score) plays
  where
    -- Generate a list of all possible plays on both ends
    plays = [(domino, L) | domino <- leftPlays] ++ [(domino, R) | domino <- rightPlays]

    -- Calculate the score for a given play
    score :: (Domino, End) -> Int
    score (domino, end) = scoreBoard newBoard isLastDomino
      where
        -- Attempt to play the domino at the specified end
        Just newBoard = playDom player domino board end
        -- Check if the hand has only one domino left or not.
        isLastDomino = length hand == 1

smartPlayer :: DomsPlayer
smartPlayer hand board player scores
  | not (null (doubleTiles `intersect` leftPlays)) && fst scores < 5 && snd scores < 5 =
    (head (doubleTiles `intersect` leftPlays), L)          -- Play a double on the left if available and scores are low(less risk)
  | not (null (doubleTiles `intersect` rightPlays)) && fst scores < 5 && snd scores < 5 =
    (head (doubleTiles `intersect` rightPlays), R)         -- Play a double on the right if available and scores are low(less risk)
  | not (null (heavyTiles `intersect` leftPlays)) && fst scores < 10 && snd scores < 10 =
    (head (heavyTiles `intersect` leftPlays), L)           -- Play a heavy domino on the left if available and scores are moderate(less risk)
  | not (null (heavyTiles `intersect` rightPlays)) && fst scores < 10 && snd scores < 10 =
    (head (heavyTiles `intersect` rightPlays), R)          -- Play a heavy domino on the right if available and scores are moderate(less risk)
  | otherwise =
    highestScoringPlay (possPlays hand board) hand board player  -- If no specific conditions are met, play the highest-scoring move available
  where
    (leftPlays, rightPlays) = possPlays hand board          -- Determine available plays on the left and right ends
    doubleTiles = filter (uncurry (==)) hand                -- Find all double Tiles (1, 1) (5, 5) etc.. in the player's hand
    heavyTiles = filter (\(a, b) -> a > 3 && b > 3) hand    -- Find dominoes with pips greater than 3 in both halves

simplePlayer :: DomsPlayer
simplePlayer hand board player scores
  | not (null leftPlays) = (head leftPlays, L)  -- If left plays are available, play the leftmost domino to the left.
  | not (null rightPlays) = (last rightPlays, R)  -- If only right plays are available, play the rightmost possible domino to the right.
  | otherwise = error "No valid moves available."  --no valid moves are available, raise an error.(not neccassry to check, better to be safe)

  where
    (leftPlays, rightPlays) = possPlays hand board  -- Calculate possible plays for both ends.

main :: IO ()
main = do
  putStrLn "tests for scoreBoard:"
  let board = InitState
  putStrLn $ "Score 1: Expected output: 0 ->" ++ show (scoreBoard board False) -- Expected output: 0

  let board = State (1, 2) (4, 2) [((1, 2), P1, 1), ((2, 2), P2, 2), ((4, 2), P1, 3)]
  putStrLn $ "Score 2: Expected output: 2 -> " ++ show (scoreBoard board True) -- Expected output: 2

  let board = State (4, 5) (5, 1) [((4, 5), P1, 1), ((5, 1), P2, 2)]
  putStrLn $ "Score 3 Expected output: 1 -> " ++ show (scoreBoard board False) -- Expected output: 1

  let board = State (4, 5) (5, 1) [((4, 5), P1, 1), ((5, 5), P2, 3)]
  putStrLn $ "Score 4: Expected output: 2 -> " ++ show (scoreBoard board True) -- Expected output: 2

  let board = State (4, 5) (4, 5) [((4, 5), P1, 1)]
  putStrLn $ "Score 5: Expected output: 3 -> " ++ show (scoreBoard board False) -- Expected output: 3

  let board = State (4, 5) (4, 5) [((4, 5), P1, 1)]
  putStrLn $ "Score 6: Expected output: 4 -> " ++ show (scoreBoard board True) -- Expected output: 4

  putStrLn "------------------------------------------"

  putStrLn "tests for blocked:"
  let board = State (4, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let hand = [(1, 2), (3, 4), (6, 6)]
  putStrLn $ "blocked 1: Expected output: False -> " ++ show (blocked hand board)

  let board = State (4, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let hand = [(1, 2), (3, 4), (6, 6)]
  putStrLn $ "blocked 2: Expected output: False -> " ++ show (blocked hand board)

  let board = State (4, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let hand = [(4, 2), (3, 4), (6, 6)]
  putStrLn $ "blocked 3: Expected output: False -> " ++ show (blocked hand board)

  let board = InitState
  let hand = [(4, 2), (3, 4), (6, 6)]
  putStrLn $ "blocked 4: Expected output: False -> " ++ show (blocked hand board)

  let board = State (4, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let hand = []
  putStrLn $ "blocked 5: Expected output: True -> " ++ show (blocked hand board)

  let board = State (4, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let hand = [(1, 2), (3, 3), (5, 2)]
  putStrLn $ "blocked 6: Expected output: True -> " ++ show (blocked hand board)
  putStrLn "------------------------------------------"

  putStrLn "tests for playDom:"
  let player = P1
  let domino = (1, 2)
  let board = State (4, 5) (6, 6) [((4, 5), P2, 2), ((5, 6), P1, 1)]
  let end = L

  putStrLn $ "playDom 1: Expected output: Nothing -> " ++ show (playDom player domino board end)

  let player = P1
  let domino = (1, 2)
  let board = State (2, 3) (6, 6) [((4, 5), P2, 2), ((5, 6), P1, 1)]
  let end = L

  putStrLn $ "playDom 2: Expected output: Just (State (1,2) (6,6) [((1,2),P1,3),((4,5),P2,2),((5,6),P1,1)]) -> " ++ show (playDom player domino board end)

  let player = P1
  let domino = (1, 6)
  let board = State (2, 3) (6, 6) [((4, 5), P2, 2), ((5, 6), P1, 1)]
  let end = R

  putStrLn $ "playDom 3: Expected output: Just (State (2,3) (6,1) [((1,6),P1,3),((4,5),P2,2),((5,6),P1,1)]) -> " ++ show (playDom player domino board end)

  let player = P1
  let domino = (1, 6)
  let board = InitState
  let end = R
  putStrLn $ "playDom 4: Expected output: Just (State (1,6) (1,6) [((1,6),P1,1)]) -> " ++ show (playDom player domino board end)

  let player = P1
  let domino = (1, 4)
  let board = State (2, 3) (3, 4) [((4, 5), P2, 2), ((5, 6), P1, 1)]
  let end = R

  putStrLn $ "playDom 5: Expected output: Just (State (2,3) (4,1) [((1,4),P1,3),((4,5),P2,2),((5,6),P1,1)]) -> " ++ show (playDom player domino board end)

  let player = P1
  let domino = (2, 6)
  let board = State (2, 3) (3, 4) [((4, 5), P2, 2), ((5, 6), P1, 1)]
  let end = L

  putStrLn $ "playDom 6: Expected output: Just (State (6,2) (3,4) [((2,6),P1,3),((4,5),P2,2),((5,6),P1,1)]) -> " ++ show (playDom player domino board end)

  let player = P2
  let domino = (2, 6)
  let board = State (2, 3) (3, 4) [((5, 6), P1, 1)]
  let end = L

  putStrLn $ "playDom 7: Expected output: Just (State (6,2) (3,4) [((2,6),P2,2),((5,6),P1,1)]) -> " ++ show (playDom player domino board end)

  putStrLn "------------------------------------------"

  putStrLn "tests for played:"
  let domino = (1, 6)
  let board = InitState
  putStrLn $ "played 1: Expected output: False -> " ++ show (played domino board)

  let domino = (1, 6)
  let board = State (1, 6) (6, 6) [((1, 6), P2, 2), ((6, 5), P2, 2), ((5, 6), P1, 1)]
  putStrLn $ "played 2: Expected output: True -> " ++ show (played domino board)

  let domino = (1, 6)
  let board = State (2, 6) (6, 6) [((2, 6), P2, 2), ((6, 5), P2, 2), ((5, 6), P1, 1)]
  putStrLn $ "played 3: Expected output: False -> " ++ show (played domino board)

  let domino = (3, 6)
  let board = State (2, 6) (6, 6) [((2, 6), P2, 2), ((6, 5), P2, 2), ((5, 6), P1, 1)]
  putStrLn $ "played 4: Expected output: False -> " ++ show (played domino board)

  putStrLn "------------------------------------------"

  putStrLn "tests for canPlayAtEnd:"

  let domino = (1, 6)
  let board = State (2, 6) (6, 6) [((2, 6), P2, 2), ((6, 5), P2, 2), ((5, 6), P1, 1)]
  let end = L

  putStrLn $ "canPlayAtEnd 1: Expected output: False -> " ++ show (canPlayAtEnd domino board end)

  let domino = (1, 6)
  let board = State (2, 6) (6, 6) [((2, 6), P2, 2), ((6, 5), P2, 2), ((5, 6), P1, 1)]
  let end = R

  putStrLn $ "canPlayAtEnd 2: Expected output: True -> " ++ show (canPlayAtEnd domino board end)

  let domino = (1, 6)
  let board = InitState
  let end = R

  putStrLn $ "canPlayAtEnd 3: Expected output: True -> " ++ show (canPlayAtEnd domino board end)

  let domino = (6, 2)
  let board = State (2, 6) (6, 6) [((2, 6), P2, 2), ((6, 5), P2, 2), ((5, 6), P1, 1)]
  let end = L

  putStrLn $ "canPlayAtEnd 4: Expected output: True -> " ++ show (canPlayAtEnd domino board end)

  putStrLn "tests for possPlays:"

  let board = State (3, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let hand = [(4, 3), (3, 4), (4, 6), (6, 2)]

  putStrLn $ "possPlays 1: Expected output: ([(4,3),(3,4)],[(4,6),(6,2)])-> " ++ show (possPlays hand board)

  let board = State (0, 0) (0, 0) []
  let hand = [(1, 1), (2, 2)]
  putStrLn $ "possPlays 2: Expected output: ([],[])-> " ++ show (possPlays  hand board)

  let board = State (3, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let hand = [(2, 3), (3, 3), (6, 6), (6, 6)]
  putStrLn $ "possPlays 3: Expected output: ([(2,3),(3,3)],[(6,6),(6,6)]) -> " ++ show (possPlays  hand board)

  let board = InitState
  let hand = [(2, 3), (3, 3), (6, 6), (6, 6)]

  putStrLn $ "possPlays 4 Expected output: ([(2,3),(3,3),(6,6),(6,6)],[(2,3),(3,3),(6,6),(6,6)])-> " ++ show (possPlays hand board)

  let board = State (3, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let hand = []
  putStrLn $ "possPlays 5: Expected output: ([],[]) -> " ++ show (possPlays  hand board)


  putStrLn "tests for doms2scoreN:"

  let board = State (3, 5) (6, 6) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let n = 2
  putStrLn $ "doms2scoreN 1: Expected output: [((3,0),L),((4,3),L),((6,3),R)] -> " ++ show (doms2scoreN board n)

  let board = State (4, 2) (6, 2) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let n = 3
  putStrLn $ "doms2scoreN 2: Expected output: [((5,2),R)] -> " ++ show (doms2scoreN board n)

  let board = State (4, 2) (6, 2) [((4, 5), P1, 1), ((5, 6), P2, 2)]
  let n = 5
  putStrLn $ "doms2scoreN 3: Expected output: [] -> " ++ show (doms2scoreN board n)

  putStrLn "tests for highestScoringPlay:"

  let board = InitState
  let hand = [(1, 2), (3, 4), (5, 6)]
  let dominos = possPlays hand board

  putStrLn $ "highestScoringPlay 1: Expected output:  ((1,2),R) -> " ++ show (highestScoringPlay dominos hand board P1)

  let board = InitState
  let hand = [(1, 2), (3, 4), (3, 6)]
  let dominos = possPlays hand board

  putStrLn $ "highestScoringPlay 2: Expected output:  ((3,6),R) -> " ++ show (highestScoringPlay dominos hand board P1)


  let board = InitState
  let hand = [(1, 1), (2, 2), (3, 1)]
  let dominos = possPlays hand board

  putStrLn $ "highestScoringPlay 3: Expected output: ((3,1),R) -> " ++ show (highestScoringPlay dominos hand board P1)

  let board = InitState
  let hand = [(1, 1), (4, 1), (3, 6)]
  let dominos = possPlays hand board

  putStrLn $ "highestScoringPlay 4: Expected output: ((3,6),R) -> " ++ show (highestScoringPlay dominos hand board P1)

