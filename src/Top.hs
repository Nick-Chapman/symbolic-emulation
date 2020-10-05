
module Top
  ( main
  , runInteractionIO
  ) where

import Control.Monad (ap,liftM)
import Data.Map (Map)
import Data.Maybe (fromMaybe)
import qualified Data.List as List
import qualified Data.Map as Map

main :: IO ()
main = do
  putStrLn "*symbolic-emulation*"

  putStrLn $ "prog1: " <> show (check [Byte n | n <- [-2,-1,0,99]] $ runProg prog1 [Byte (-3)])
  putStrLn $ "prog2: " <> show (check [Byte 42] $ runProg prog2 [Byte 6, Byte 7])

  --runInteractionIO [Byte (-10)] 15 (emulate prog1)
  --runInteractionIO [Byte 6, Byte 7] 0 (emulate prog2)

  let _ = prog0

  --let (p,inp) = (prog0,[Byte 10, Byte 20] )
  --let (p,inp) = (prog1,[Byte (-5)])
  let (p,inp) = (prog2,[Byte 3, Byte 10])

  putStrLn "emulate"
  runInteractionIO inp 0 (emulate p)

  putStrLn "compile..."
  let gen = compile p
  print gen
  putStrLn "run..."
  runInteractionIO inp 0 (runGen gen)


check :: (Eq a, Show a) => a -> a -> a
check x y = if x == y then x else error (show (x,y))


runProg :: Prog -> [Byte] -> [Byte]
runProg prog xs = runInteraction xs (emulate prog)

data Interaction a s
  = I_Stop
  | I_Internal s (Interaction a s)
  | I_Output a (Interaction a s)
  | I_Input (a -> Interaction a s)

runInteraction :: [a] -> Interaction a s -> [a]
runInteraction = loop []
  where
    loop :: [a] -> [a] -> Interaction a s -> [a]
    loop os xs = \case
      I_Stop -> reverse os
      I_Internal _s next -> loop os xs next
      I_Input f -> case xs of
        [] -> error "runInteraction, run out of input"
        x:xs -> loop os xs (f x)
      I_Output o next -> loop (o:os) xs next

runInteractionIO :: (Show d, Show s) => [d] -> Int -> Interaction d s -> IO ()
runInteractionIO = loop
  where
    loop :: (Show d, Show s) => [d] -> Int -> Interaction d s -> IO ()
    loop xs limit = \case
      I_Stop -> putStrLn "**interaction, stop"
      I_Internal _s next -> do
        --putStrLn $ "**internal state: " <> show _s
        loop xs limit next
      I_Input f -> case xs of
        [] -> do putStrLn "**interaction, run out of input"
        x:xs -> loop xs limit  (f x)
      I_Output d next -> do
        putStrLn $ "**output: " <> show d
        if (limit==1)
          then putStrLn $ "**output limit reached"
          else loop xs (limit-1) next

newtype Immediate = Immediate Int

prog0 :: Prog
prog0 = makeProg
  [ NOP
  , INP
  , XCH A B
  , INP
  , ADD
  , OUT
  , HLT
  ]

prog1 :: Prog
prog1 = makeProg -- count up from input, printing incrementing numbers, until we reach 0
  [ NOP
  , LDI (Immediate 1)
  , XCH A B
  , INP
  -- label 4
  , ADD
  , OUT
  , XCH A C
  , LDI (Immediate 4)
  , XCH A C
  , JNZ
  , LDI (Immediate 99)
  , OUT
  ]

prog2 :: Prog -- multiply 2 inputs
prog2 = makeProg
  [ INP
  , XCH A B
  , INP
  -- label 3
  , XCH A C , LDI (Immediate 10) , XCH A C , JNZ
  , XCH A D
  , OUT
  , HLT
  -- label 10
  , DEC
  , XCH A D
  , ADD
  , XCH A D
  , XCH A C , LDI (Immediate 3) , XCH A C , JMP
  ]

data Instruction
  = HLT
  | NOP
  | LDI Immediate -- in reality this would be in the next address
  | INP
  | OUT
  | XCH Reg Reg
  | DEC
  | ADD
  | JMP
  | JNZ

data Flow a = Halt | Next | Jump a

data Ops a = Ops
  { add :: a -> a -> a
  , dec :: a -> a
  , lit :: Int -> a
  }

semantics :: Ops a -> Instruction -> Eff a (Flow a)
semantics Ops{add,dec,lit} = \case
  HLT -> do
    return Halt

  NOP -> do
    return Next

  LDI (Immediate n) -> do
    SetReg A (lit n)
    return Next

  INP -> do
    i <- Inp
    SetReg A i
    return Next

  OUT -> do
    a <- GetReg A
    Out a
    return Next

  XCH r1 r2 -> do
    x <- GetReg r1
    y <- GetReg r2
    SetReg r2 x
    SetReg r1 y
    return Next

  DEC -> do
    a <- GetReg A
    SetReg A (dec a)
    return Next

  ADD -> do
    a <- GetReg A
    b <- GetReg B -- implicity takes uses B for 2nd arg of addition
    SetReg A (add a b)
    return Next

  JMP -> do
    dest <- GetReg C -- implicitly uses C as the jump dest
    return (Jump dest)

  JNZ -> do
    a <- GetReg A -- implicitly uses A for the zero-test
    bool <- IsZero a
    if bool then return Next else do
      dest <- GetReg C -- implicitly uses C as the jump dest
      return (Jump dest)


instance Functor (Eff d) where fmap = liftM
instance Applicative (Eff d) where pure = return; (<*>) = ap
instance Monad (Eff d) where return = Ret; (>>=) = Bind

data Eff d a where
  Ret :: a -> Eff d a
  Bind :: Eff d a -> (a -> Eff d b) -> Eff d b
  Inp :: Eff d d
  Out :: d -> Eff d ()
  GetReg :: Reg -> Eff d d
  SetReg :: Reg -> d -> Eff d ()
  IsZero :: d -> Eff d Bool

data Reg = A | B | C | D
  deriving (Eq, Show)

allRegs :: [Reg] -- TODO, do this via derving something
allRegs = [A,B,C,D]

data CpuState a = CpuState
  { regA :: a
  , regB :: a
  , regC :: a
  , regD :: a
  }

initCpuState :: a -> CpuState a
initCpuState x = CpuState
  { regA = x
  , regB = x
  , regC = x
  , regD = x
  }

cpuState0 :: CpuState Byte
cpuState0 = initCpuState (Byte 0)


getReg :: CpuState a -> Reg -> a
getReg CpuState{regA,regB,regC,regD} = \case
  A -> regA
  B -> regB
  C -> regC
  D -> regD

setReg :: CpuState a -> a -> Reg -> CpuState a
setReg s x = \case
  A -> s { regA = x }
  B -> s { regB = x }
  C -> s { regC = x }
  D -> s { regD = x }

instance Show a => Show (CpuState a) where
  show CpuState{regA,regB,regC,regD} = show (regA,regB,regC,regD)


data Prog = Prog { fetch :: Addr -> Instruction }

makeProg :: [Instruction] -> Prog
makeProg xs = Prog f
  where f a = fromMaybe HLT (Map.lookup a m)
        m :: Map Addr Instruction = Map.fromList [ (Addr n, x) | (n,x) <- zip [0..] xs ]


type IBC = Interaction Byte (Addr,CpuState Byte)

emulate :: Prog -> IBC
emulate prog = runStar cpuState0 (Addr 0)
  where

    runStar :: CpuState Byte -> Addr -> IBC
    runStar s a =
      I_Internal (a,s) $
      run s (semantics opsByte (fetch prog a)) afterwards
      where
        afterwards :: CpuState Byte -> Flow Byte -> IBC
        afterwards s = \case
          Halt -> I_Stop
          Jump b -> runStar s (addrOfByte b)
          Next -> runStar s (nextAddr a)

    run :: CpuState Byte -> Eff Byte a -> (CpuState Byte -> a -> IBC) -> IBC
    run s act k = case act of
      Ret x -> k s x
      Bind eff f -> run s eff $ \s a -> run s (f a) k
      Inp -> I_Input $ \i -> k s i
      Out d -> I_Output d (k s ())
      GetReg reg -> k s (getReg s reg)
      SetReg reg x -> k (setReg s x reg) ()
      IsZero byte -> k s (isZeroByte byte)


newtype Addr = Addr Int
  deriving (Eq,Ord)
instance Show Addr where show (Addr n) = "#" <> show n

nextAddr :: Addr -> Addr
nextAddr (Addr n) = Addr (n+1)

addrOfByte :: Byte -> Addr
addrOfByte (Byte n) = Addr n


newtype Byte = Byte Int
  deriving Eq
instance Show Byte where show (Byte n) = show n

byteOfInt :: Int -> Byte
byteOfInt = Byte

isZeroByte :: Byte -> Bool
isZeroByte (Byte n) = n==0

decByte :: Byte -> Byte
decByte (Byte n) = Byte (n-1)

addByte :: Byte -> Byte -> Byte
addByte (Byte b1) (Byte b2) = Byte (b1+b2)

opsByte :: Ops Byte
opsByte = Ops
  { add = addByte
  , dec = decByte
  , lit = byteOfInt
  }

----------------------------------------------------------------------

data CompileState = CS
  { cpuState :: CpuState Exp
  , nextVar :: Int
  }

compile :: Prog -> GenProg
compile prog = GP (Map.fromList [(lab, compileLab lab) | lab <- reachable ])
  where

    reachable :: [Lab]
    reachable = step [Lab startAddr] [Lab startAddr]
      where
        startAddr = Addr 0
        step :: [Lab] -> [Lab] -> [Lab]
        step acc xs = do
          let xs' = [ y
                    | x <- xs
                    , y <- statLabels (compileLab x)
                    , not (List.elem y acc)
                    ]
          if xs' == [] then acc else
            step (acc ++ xs') xs'

    compileLab :: Lab -> Stat
    compileLab (Lab a) = runStar state0 a

    state0 :: CompileState
    state0 = CS { nextVar = 1, cpuState = cpuState0 }

    cpuState0 :: CpuState Exp
    cpuState0 = CpuState
      { regA = E_Reg A
      , regB = E_Reg B
      , regC = E_Reg C
      , regD = E_Reg D
      }

    runStar :: CompileState -> Addr -> Stat
    runStar s@CS{cpuState} a =
      run s (semantics opsExp (fetch prog a)) afterwards
      where
        afterwards :: CompileState -> Flow Exp -> Stat
        afterwards s = \case
          Halt -> S_Null
          Next -> runStar s (nextAddr a)
          Jump exp ->
            --runStar s (addrOfByte (byteOfExp exp))
            S_Assign regUpdates $
            S_Jump (Lab (addrOfByte (byteOfExp exp)))

        regUpdates :: [(Reg,Exp)]
        regUpdates =
          [(r,exp)
          | r <- allRegs
          , let exp = getReg cpuState r
          , not (exp == E_Reg r)
          ]

    run :: CompileState -> Eff Exp a -> (CompileState -> a -> Stat) -> Stat
    run s@(CS{cpuState,nextVar}) act k = case act of
      Ret x -> k s x
      Bind eff f -> run s eff $ \s a -> run s (f a) k
      Inp -> do
        let v = Var nextVar
        S_LetInput v (k s { nextVar = nextVar + 1 } (E_Var v))
      Out exp -> S_Output exp (k s ())
      GetReg reg -> k s (getReg cpuState reg)
      SetReg reg x -> k (s { cpuState = setReg cpuState x reg }) ()
      IsZero exp ->
        S_IsZero exp (k s True) (k s False) -- call continutaion twice!


data GenProg = GP (Map Lab Stat)

data Stat
  = S_Null
  | S_Output Exp Stat
  | S_LetInput Var Stat
  | S_IsZero Exp Stat Stat
  | S_Assign [(Reg, Exp)] Stat
  | S_Jump Lab

newtype Lab = Lab Addr
  deriving (Eq, Ord)

data Exp
  = E_Lit Byte
  | E_Var Var
  | E_Reg Reg
  | E_Dec Exp
  | E_Add Exp Exp
  deriving (Eq)

newtype Var = Var Int
  deriving (Eq,Ord)


opsExp :: Ops Exp
opsExp = Ops
  { add = addExp
  , dec = decExp
  , lit = E_Lit . byteOfInt
  }

decExp :: Exp -> Exp
decExp = \case
  -- E_Lit b -> E_Lit (decByte b) -- necessary?
  e -> E_Dec e

addExp :: Exp -> Exp -> Exp
addExp e1 e2 = case (e1,e2) of
  -- TODO: special cases?
  _ -> E_Add e1 e2

byteOfExp :: Exp -> Byte
byteOfExp = \case
  E_Lit byte -> byte
  e -> error $ "byteOfExp: " <> show e



statLabels :: Stat -> [Lab]
statLabels = \case
  S_Null -> []
  S_Output _ stat -> statLabels stat
  S_LetInput _ stat -> statLabels stat
  S_Jump lab -> [lab]
  S_IsZero _ s1 s2 -> statLabels s1 ++ statLabels s2
  S_Assign _ s -> statLabels s


instance Show GenProg where show = unlines . prettyGenProg
instance Show Stat where show = unlines . prettyStat
instance Show Exp where show = prettyExp
instance Show Var where show (Var n) = "v" ++ show n
instance Show Lab where show (Lab a) = "lab" ++ show a

prettyGenProg :: GenProg -> [String]
prettyGenProg (GP m) =
  concat [ [show lab ++ ":"] ++ indent (prettyStat stat) | (lab,stat) <- Map.toList m ]

prettyStat :: Stat -> [String]
prettyStat = \case
  S_Null -> []
  S_Output exp stat -> ("output(" ++ show exp ++ ")") : prettyStat stat
  S_LetInput var stat -> ("let " ++ show var ++ " = input()") : prettyStat stat
  S_Jump lab -> ["jump: " ++ show lab]
  S_IsZero e s1 s2 ->
    [ "if (isZero(" ++ show e ++ ")) {"
    ] ++ indent (prettyStat s1)  ++
    [ "} else {"
    ] ++ indent (prettyStat s2) ++
    [ "}"
    ]
  S_Assign binds s ->
    [  show (map fst binds) ++ ":=" ++ show (map snd binds) ] ++
    prettyStat s

indent :: [String] -> [String]
indent lines = ["  " ++ line | line <- lines ]

prettyExp :: Exp -> String
prettyExp = \case
  E_Lit byte -> show byte
  E_Var var -> show var
  E_Reg r -> show r
  E_Dec e -> brac (show e ++ "-1")
  E_Add e1 e2 -> brac (show e1 ++ "+" ++ show e2)
  where brac s = "("++s++")"


type IBU = Interaction Byte ()

data Env = Env
  { vars :: Map Var Byte
  , regs :: CpuState Byte
  }

runGen :: GenProg -> IBU
runGen (GP m) = execStat q0 (lookAddr (Lab startAddr))
  where
    q0 = Env { vars = Map.empty, regs = cpuState0 }

    startAddr = Addr 0

    lookAddr :: Lab -> Stat
    lookAddr lab = fromMaybe (error $ "lookAddr:"++show lab) (Map.lookup lab m)

    execStat :: Env -> Stat -> IBU
    execStat q@Env{vars,regs} = \case
      S_Null -> I_Stop
      S_Output exp stat -> I_Output (evalExp q exp) (execStat q stat)
      S_LetInput var stat ->
        I_Input $ \byte -> execStat (q { vars = Map.insert var byte vars}) stat
      S_IsZero e s1 s2 -> execStat q (if isZeroByte (evalExp q e) then s1 else s2)
      S_Jump lab -> execStat q (lookAddr lab)
      S_Assign pairs s -> execStat q {regs = regs'} s
        where
          regs' = foldr update regs [ (r, evalExp q e) | (r,e) <- pairs ]
          update :: (Reg,Byte) -> CpuState Byte -> CpuState Byte
          update (r,e) cpuState = setReg cpuState e r

evalExp :: Env -> Exp -> Byte
evalExp q@Env{vars,regs} = \case
  E_Lit byte -> byte
  E_Var var -> fromMaybe (error $ "evalExp:"++show var) (Map.lookup var vars)
  E_Reg reg -> getReg regs reg
  E_Dec exp -> decByte (evalExp q exp)
  E_Add e1 e2 -> addByte (evalExp q e1) (evalExp q e2)
