
module Top (main,runInteractionIO) where

import Control.Monad (ap,liftM)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.Map as Map

main :: IO ()
main = do
  putStrLn "*symbolic-emulation*"

  putStrLn $ "prog1: " <> show (check [Byte n | n <- [-2,-1,0,99]] $ runProg prog1 [Byte (-3)])
  putStrLn $ "prog2: " <> show (check [Byte 42] $ runProg prog2 [Byte 6, Byte 7])

  --runInteractionIO [Byte (-10)] 15 (emulate prog1)
  --runInteractionIO [Byte 6, Byte 7] 0 (emulate prog2)


check :: (Eq a, Show a) => a -> a -> a
check x y = if x == y then x else error (show (x,y))


runProg :: Prog -> [Byte] -> [Byte]
runProg prog xs = runInteraction xs (emulate prog)

data Interaction a s
  = Stop
  | Internal s (Interaction a s)
  | Output a (Interaction a s)
  | Input (a -> Interaction a s)

runInteraction :: [a] -> Interaction a s -> [a]
runInteraction = loop []
  where
    loop :: [a] -> [a] -> Interaction a s -> [a]
    loop os xs = \case
      Stop -> reverse os
      Internal _s next -> loop os xs next
      Input f -> case xs of
        [] -> error "runInteraction, run out of input"
        x:xs -> loop os xs (f x)
      Output o next -> loop (o:os) xs next

runInteractionIO :: (Show d, Show s) => [d] -> Int -> Interaction d s -> IO ()
runInteractionIO = loop
  where
    loop :: (Show d, Show s) => [d] -> Int -> Interaction d s -> IO ()
    loop xs limit = \case
      Stop -> putStrLn "**interaction, stop"
      Internal _s next -> do
        putStrLn $ "**internal state: " <> show _s
        loop xs limit next
      Input f -> case xs of
        [] -> do putStrLn "**interaction, run out of input"
        x:xs -> loop xs limit  (f x)
      Output d next -> do
        putStrLn $ "**output: " <> show d
        if (limit==1)
          then putStrLn $ "**output limit reached"
          else loop xs (limit-1) next

newtype Immediate = Immediate Int

prog1 :: Prog
prog1 = makeProg -- count up from input, printing incrementing numbers, until we reach 0
  [ NOP
  , LDI (Immediate 1)
  , XAB
  , INP
  -- label 4
  , ADD
  , OUT
  , XAC
  , LDI (Immediate 4)
  , XAC
  , JNZ
  , LDI (Immediate 99)
  , OUT
  ]

prog2 :: Prog -- multiply 2 inputs
prog2 = makeProg
  [ INP
  , XAB
  , INP
  -- label 3
  , XAC , LDI (Immediate 10) , XAC , JNZ
  , XAD
  , OUT
  , HLT
  -- label 10
  , DEC
  , XAD
  , ADD
  , XAD
  , XAC , LDI (Immediate 3) , XAC , JMP
  ]

data Instruction
  = HLT
  | NOP
  | LDI Immediate -- in reality this would be in the next address
  | INP
  | OUT
  | XAB
  | XAC
  | XAD
  | DEC
  | ADD
  | JMP
  | JNZ

data Flow = Halt | Next | Jump Addr

semantics :: Instruction -> Eff Flow
semantics = \case
  HLT -> do
    return Halt

  NOP -> do
    return Next

  LDI (Immediate n) -> do
    SetA (Byte n)
    return Next

  INP -> do
    i <- Inp
    SetA i
    return Next

  OUT -> do
    a <- GetA
    Out a
    return Next

  XAB -> do
    a <- GetA
    b <- GetB
    SetA b
    SetB a
    return Next

  XAC -> do
    a <- GetA
    c <- GetC
    SetA c
    SetC a
    return Next

  XAD -> do
    a <- GetA
    d <- GetD
    SetA d
    SetD a
    return Next

  DEC -> do
    a <- GetA
    SetA (decByte a)
    return Next

  ADD -> do
    a <- GetA
    b <- GetB -- implicity takes uses B for 2nd arg of addition
    SetA (addByte a b)
    return Next

  JMP -> do
    Byte n <- GetC -- implicitly uses C as the jump dest
    return (Jump (Addr n))

  JNZ -> do
    a <- GetA -- implicitly uses A for the zero-test
    if isZeroByte a then return Next else do
      Byte n <- GetC -- implicitly uses C as the jump dest
      return (Jump (Addr n))


instance Functor Eff where fmap = liftM
instance Applicative Eff where pure = return; (<*>) = ap
instance Monad Eff where return = Ret; (>>=) = Bind

data Eff a where -- Eff d a -- TODO: generlise Byte --> d
  Ret :: a -> Eff a
  Bind :: Eff a -> (a -> Eff b) -> Eff b
  Inp :: Eff Byte
  Out :: Byte -> Eff ()
  GetA :: Eff Byte -- TODO: share Get/Set with data Reg = A|B|C
  SetA :: Byte -> Eff ()
  GetB :: Eff Byte
  SetB :: Byte -> Eff ()
  GetC :: Eff Byte
  SetC :: Byte -> Eff ()
  GetD :: Eff Byte
  SetD :: Byte -> Eff ()


data CpuState = CpuState
  { regA :: Byte
  , regB :: Byte
  , regC :: Byte
  , regD :: Byte
  }

instance Show CpuState where
  show CpuState{regA,regB,regC,regD} = show (regA,regB,regC,regD)

cpuState0 :: CpuState
cpuState0 = CpuState
  { regA = Byte 0
  , regB = Byte 0
  , regC = Byte 0
  , regD = Byte 0
  }


data Prog = Prog { fetch :: Addr -> Instruction }

makeProg :: [Instruction] -> Prog
makeProg xs = Prog f
  where f a = fromMaybe HLT (Map.lookup a m)
        m :: Map Addr Instruction = Map.fromList [ (Addr n, x) | (n,x) <- zip [0..] xs ]


type IBC = Interaction Byte (Addr,CpuState)

emulate :: Prog -> IBC
emulate prog = runStar cpuState0 startAddr
  where
    startAddr = Addr 0

    runStar :: CpuState -> Addr -> IBC
    runStar s a =
      Internal (a,s) $
      run s (semantics (fetch prog a)) afterwards
      where
        afterwards :: CpuState -> Flow -> IBC
        afterwards s = \case
          Halt -> Stop
          Jump a -> runStar s a
          Next -> runStar s (nextAddr a)

    run :: CpuState -> Eff a -> (CpuState -> a -> IBC) -> IBC
    run s@CpuState{regA,regB,regC,regD} act k = case act of
      Ret x -> k s x
      Bind eff f -> run s eff $ \s a -> run s (f a) k
      Inp -> Input $ \i -> k s i
      Out d -> Output d (k s ())
      GetA -> k s regA
      SetA x -> k (s { regA = x }) ()
      GetB -> k s regB
      SetB x -> k (s { regB = x }) ()
      GetC -> k s regC
      SetC x -> k (s { regC = x }) ()
      GetD -> k s regD
      SetD x -> k (s { regD = x }) ()


newtype Addr = Addr Int
  deriving (Eq,Ord)
instance Show Addr where show (Addr n) = "#" <> show n

nextAddr :: Addr -> Addr
nextAddr (Addr n) = Addr (n+1)


newtype Byte = Byte Int
  deriving Eq
instance Show Byte where show (Byte n) = show n

isZeroByte :: Byte -> Bool
isZeroByte (Byte n) = n==0

decByte :: Byte -> Byte
decByte (Byte n) = Byte (n-1)

addByte :: Byte -> Byte -> Byte
addByte (Byte b1) (Byte b2) = Byte (b1+b2)
