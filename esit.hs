--module esit where

-- (parseResult,  parseEqString, runSolvr)

import Data.Char (isNumber,isSpace)
import Data.List (partition)
import Control.Monad (liftM,liftM2)


--- maybe2: returns Just if both maybes are a Just or nothing otherwise
maybe2 :: Maybe a -> Maybe b -> Maybe (a,b)
maybe2 =  liftM2 (,)

--- expressions 
data Expr  =  Var | Value Int | Cval Int Expr | 
              Add Expr Expr | Sub Expr Expr |
              Div Expr Expr -- deriving Show

--- displaying equations
display :: Expr -> String
display Var       =  "x"
display (Value n) = show n
display (Cval n e) = show n ++ display e
display (Add l r) = display l ++ "+" ++ display r
display (Sub l r) = display l ++ "-" ++ display r
display (Div x y) = display x ++ "/" ++ display y

instance Show Expr where
   show  = display

--interpreting equations
eval :: Expr -> Double -> Double
eval  Var       n   =  n
eval  (Value n) _   =  fromIntegral n
eval  (Cval n e) m  =  fromIntegral n * eval e m
eval  (Add l r) m   =  eval l m + eval r m
eval  (Sub l r) m   =  eval l m - eval r m
eval  (Div l r) m   =  eval l m / eval r m

-- equality of linear equations
eEqual :: Expr -> Expr -> Bool
eEqual  e1  e2   = eval e1 0 == eval e2 0 && eval e1 1 == eval e2 1  

instance Eq Expr where
     (==) = (eEqual)  

-- is the expression a variable
isVar :: Expr -> Bool
isVar Var          = True
isVar (Cval _ Var) = True
isVar    x         = False

isNeg :: Expr -> Bool
isNeg (Value n)   = n < 0
isNeg (Cval n _ ) = n < 0
isNeg    _        = False

-- if the expression has a value
isVal :: Expr -> Bool
isVal (Value _)    = True
isVal _            = False

canComp :: Expr -> Expr -> Bool
canComp  l r = (isVar l && isVar r) || (isVal l && isVal r)

--
isVSubs, isLSubs :: Expr -> Bool
isVSubs (Sub a b)  
    | canComp a b           =  True
    | isVar a               =  isVSubs b
    | otherwise             =  False
isVSubs   _                 =  False

isLSubs (Sub a b)  
    | canComp a b           =  True
    | isVal a               =  isLSubs b
    | otherwise             =  False
isLSubs   _                 =  False


--- rewrites (Sub a (Sub b (Sub c) d) k) ->  Sub (Sub a  b) (Sub (Sub c d) k)
--- if a b c and d are the same type
trnSubs :: Expr -> Expr
trnSubs s@(Sub a b)
    | canComp a b   =  s 
    | otherwise     = case b of
                        Sub p q -> if canComp a p  
                                   then (Sub (Sub a p) (trnSubs q)) 
                                   else case p of
                                         Add r s -> if canComp a r  
                                                    then Sub (Sub a r) (Add s (trnAdd q))
                                                    else (Sub a (trnAdd b))
                                         _       -> (Sub a (trnSubs b))
                        _       -> Sub a (trnSubs b)
trnSubs  xs         =  xs     


--- rewrites (Add a (Add b (Add c) d) k)  ->  Add (Add a  b) (Add (Add c d) k)
--- if a b c and d are the same type
trnAdd :: Expr -> Expr
trnAdd s@(Add a b)
    | canComp a b   =  s 
    | otherwise     = case b of
                        Add p q -> if canComp a p  
                                   then (Add (Add a p) (trnAdd q))
                                   else 
                                       case p of
                                         Sub r s -> if canComp a r  
                                                    then Add (Add a r) (Sub s (trnAdd q))
                                                    else (Add a (trnAdd b))
                                         _       -> (Add a (trnAdd b))
                        _       -> Add a (trnAdd b)
trnAdd  xs         =  xs       

nComp :: Expr  -> Bool
nComp  l     =   not (isVar l ||  isVal l)

-- sytactic equality for comaparing operations
sEqual :: Expr -> Expr -> Bool
sEqual Var        Var             = True
sEqual (Value n) (Value m)        = m == n
sEqual (Cval n l) (Cval m r)      = n == m && sEqual l r
sEqual (Add l r) (Add ll rr)      = sEqual l ll && sEqual r rr
sEqual (Sub l r) (Sub ll rr)      = sEqual l ll && sEqual r rr
sEqual (Div a b) (Div c d)        = sEqual a c  && sEqual c b
sEqual    _         _             = False

-------------------------------------------------------------------------
--- Some Arithmetic operations
-------------------------------------------------------------------------
-- grouping
group :: Expr -> Expr
group  (Add l (Add ll r))      
    | isVar r && isVar ll                     = Add (add $ Add r ll) (group l)
    | isVar r                                 = Add r (group $ Add l ll)
    | isVar ll                                = Add ll (group $ Add l r)
    | isVal l && isVal ll                     = Add  (group r)  $ Add l ll
    | isVal l                                 = Add (group $ Add ll r) l
    | isVal ll                                = Add (group $ Add l r) ll                                           
    | otherwise                               = Add (group l) (group $ Add ll r)     
group  (Add (Add l ll) r)                     = group $ Add l (group $ Add ll r)
--
group (Sub l (Sub q Var))                     = (Add (Cval (-1) Var)  (group $ Sub l q))
group (Sub l (Sub q (Cval n r)))              = (Add (Cval (-n) r)  (group $ Sub l q))  
group (Sub l (Sub Var q))                     = (Add (Cval (-1) Var)  (group $ Sub l q))
group (Sub l (Sub (Cval n r) q))              = (Add (Cval (-n) r)  (group $ Sub l q))  
group (Sub l (Sub q r)) 
    |  canComp l q && (not $ canComp r q )    =  Sub (Sub  l  q) $ group r
    |  canComp l r && (not $ canComp r q )    =  
                                                 Sub l (Sub r q)
    | otherwise                               =  Sub  l (group $ Sub q  r)   
--
group (Sub (Sub l q) r)                    
    |  canComp l q &&  canComp r q               =  Sub l (Sub l q) 
--
group (Add (Sub l  ll) (Sub a b))       
    | canComp l ll                            =  group $ Add (sub $ Sub l ll) (Sub a b) 
    | canComp a b                             =  group $ Add (Sub l ll) (sub $ Sub a b)  
    | isVar l && isVar b                      =  Add (Sub l b) (Sub a ll)
    | isVar l && isVar a                      =  Sub (Add l a) (Sub ll b)
    | isVar ll && isVar a                     =  Add (Sub a ll) (Sub l b)
    | isVar ll && isVar b                     =  group $ Sub (Add l a) (add $ Add ll b)
    --
    | isVal l && isVal b                      =  Add (Sub a ll)  (Sub l b)
    | isVal l && isVal a                      =  group $ Sub (add $ Add l a) (Sub ll b)
    | isVal ll && isVal a                     =  group $ Add (sub $ Sub a ll) (Sub l b)
    | isVal ll && isVal b                     =  group $ Sub (Add l a) (add $ Add ll b)
    | otherwise                               =  Sub (group $ Add l a) (group $ Add ll b) 
--}
group (Add l (Sub ll r))                      
    | canComp l ll                            = Sub (Add l ll) $ group r
    | canComp l r                             = Add (Sub l r) $ group ll
    | isVal l                                 = Add (group $ Sub ll r) l 
    | isVar l                                 = Add l (group $ Sub ll r)                                             
    | otherwise                               = Add (group l) (group $ Sub ll  r)  
--}
group (Add (Sub l  ll) r)                       
    | canComp l r                             =  Sub (Add l r) ll
    | otherwise                               =  Add (Sub l ll) $ group r                 
--             
group (Sub l (Add ll r))                     
    | canComp l r                             =  Add (Sub l r) $ group ll  
    | otherwise                               =  Sub (group l) $ group (Add ll r)
group (Sub l r)                               =  Sub (group l) (group r)
--
group (Add l (Value n))                             
    | (isVal l || isVar l) && n < 0           = Sub l (Value (-n))
    | otherwise                               = Add (group l) (Value n)
group (Add l (Cval n r))                             
    | (isVal l || isVar l) && n < 0           = Sub l (Cval (-n) r)
    | otherwise                               = Add l (Cval n r)
group (Add l r)                               =  Add (group l) (group r) 
group  xs                                     =  xs

-- adding
add :: Expr -> Expr 
add (Add Var Var)                            = Cval 2 Var
add (Add (Value n)  (Value m))               = Value (n+m)
add (Add (Cval n Var)  (Cval m Var))         = Cval (n+m) Var
add (Add (Add (Sub l r) k) q)                = add $ Add (Sub l r) (add $ Add k q)
add (Add Var (Cval n Var))   
    | n == 0                                 = Var
    | otherwise                              = Cval (n+1) Var 
add (Add (Cval n Var) Var)   
    | n == 0                                 = Var
    | otherwise                              = Cval (n+1) Var 
--
add (Add l (Cval n k))   
    | n == 0                                = l
    | otherwise                             = Add (Cval n k) (add l) 
add (Add (Cval n k) l)   
    | n == 0                                = l
    | otherwise                             = Add (Cval n Var) (add l)
---
add (Add (Add l  r) k)                      = Add (add $ Add l r) (add k) 
-- add sub
add (Sub (Add l ll) r)                      =  Sub (add $ Add l ll) (add r)
add (Add (Sub l  r) k)                  
   | canComp l  r                           =  Add (sub $ Sub l r)  $ add k 
   | canComp k  r                           =  Add (add l) (sub $ Sub k r) 
   | canComp l  k                           =  Sub  (add $ Add l k) (add r)           
   | otherwise                              =  Add (Sub  (add l)  (add r))  (add k)
add (Add l (Sub k r))                  
   | canComp l k                            =  Sub (add (Add l k)) $ add r 
   | canComp l r                            =  Sub (add  $ Add l (add k)) $  r
   | otherwise                              =  Add (add l)  (add $ Sub (add k)  $ add r) 
--  
add (Sub l (Add ll r))                      =  Sub (add l) (add $ Add (add ll) $ add r) 
add (Add l (Add r k))                    
    | canComp l r                           =  Add (add $ Add l r) (add k)
    | canComp l k                           =  Add (add r) (add $ Add l k)        
    | otherwise                             =  Add (add l) (add $ Add  (add  r)   (add k))
--}
add (Sub l r)                               =  Sub (add l) (add r)
add (Add l r)                               =  Add (add l) (add r)
add  xs                                     =  xs

--subtracting
sub :: Expr -> Expr
sub (Sub Var Var)                           = Value 0
sub (Sub (Value n) (Value m))               = Value (n-m)
sub (Sub (Cval n Var)  (Cval m Var))        = Cval (n-m) Var
sub (Sub Var (Cval n Var))   
    | n == 1                                = Value 0
    | otherwise                             = Cval (1 - n) Var
sub (Sub (Cval n Var) Var)   
    | n == 1                                = Value 0
    | otherwise                             = Cval (n-1) Var 
sub  (Sub l (q@(Sub r k)))                                                         
    | isVSubs q || isLSubs q                =  sub $ Sub l (add $ sub2add q) 
    | canComp l  k && (not $ canComp r  k)  =  sub $ Sub (sub $ Sub l  k) r 
    | canComp r  k                          =  sub $ Sub l (add $ Add r k)  
    | otherwise                             =   sub $ Sub  l (sub $ Sub r k) 
sub (Sub q@(Sub l  r) k)         
    | isVSubs q || isLSubs q                =  sub $ Sub (add $ sub2add q) (sub k)
    | otherwise                             =  sub $ Sub (sub $ Sub l r) $ sub k
--      |
sub (Sub l (Add k r))                  
    | canComp l k                           =  Add (sub $ Sub l k) r  
    | canComp k  r  && (not $ isVar l)      =  Sub (sub l) (add $ Add  r k)
    | canComp k  r  && (not $ isVal l)     =  Sub (sub l) (add $ Add  r k)
    | otherwise                            =  Sub (sub l) (sub $ Add k r)
--
sub (Add l (Sub r k))                      = Add (sub l) (sub $ Sub r k)
sub (Add (Sub l  r) k)                     = Add (sub $ Sub l r) (sub k)
sub (Sub (Add l  r) k)                 -- = Add l (sub $ Sub r k)
    | canComp l  k  && (not $ isVar r)     =  Add (sub $ Sub l k) r
    | canComp l  k  && (not $ isVal r)     =  Add (sub $ Sub l k) r
    | canComp r  k  && (not $ isVar l)     =  Add l (sub $ Sub r k) 
    | canComp r  k  && (not $ isVal l)     =  Add l (sub $ Sub r k) 
    | otherwise                            =  Sub (sub $ Add l r) (sub k)
sub (Add  l  r)                            =  Add (sub l) (sub r)
sub (Sub  l  r)                            =  Sub (sub l) (sub r)
--
sub   xs                                   =  xs 

--
--
sub2add :: Expr -> Expr
sub2add (Sub a b) = Add (sub2add a) (sub2add b)
sub2add xs = xs

--- simplify
simplify  = simplify' 1 -- :: Int -> Expr -> Expr
simplify' :: Int -> Expr -> Expr
simplify' n ex
    | normFrm ex    = remZero ex
    | n > 100       = remZero ex                          
    | otherwise     = simplify' (n + 1) $  (group .  sub .  trnSubs .  add  . trnAdd . group . remZero) ex 
    where 
      -- rewites expressions with zeros
      remZero :: Expr -> Expr
      remZero  (Cval 0 l)                  = Value 0
      remZero  (Add l (Value 0))           = l
      remZero  (Add (Cval 0 _) l)          = l
      remZero  (Add l (Cval 0 _))          = l
      remZero  (Add (Value 0) l)           = l
      remZero  (Sub l (Value 0))           = l
      remZero  (Sub (Cval 0 _) (Value n))  = Value (-n)
      remZero  (Sub (Value 0)  Var)        = (Cval (-1) Var)
      remZero  (Sub (Value 0) (Cval n l))  = (Cval (-n) l)
      remZero        xs                   =  xs 
      --
      normFrm :: Expr -> Bool
      normFrm  Var                         = True
      normFrm  (Value _)                   = True
      normFrm  (Cval _ _)                  = True
      normFrm  (Div _ _)                   = True
      normFrm  (Add Var (Value _))         = True
      normFrm  (Add (Cval _ _) (Value _))  = True
      normFrm  (Add (Value _) Var)         = True
      normFrm  (Add (Value _) (Cval _ _))  = True
      normFrm  (Sub Var (Value _))         = True
      normFrm  (Sub (Cval _ _) (Value _))  = True
      normFrm  (Sub (Value _)  Var)        = True
      normFrm  (Sub (Value _) (Cval _ _))  = True
      normFrm  _                           = False
-------------------------------------------------------------------------

---parsing a string to equations 
parseString :: String -> Maybe Expr
parseString xs
     |  null xs                 = Nothing
     |  xs == "x"               = Just Var
     |  all isNumber xs         = Just (Value $ read xs)
     |  elem '+' xs = 
         let (front,ys) = span (/= '+') xs  in
             case maybe2 (parseString front) (parseString $ dropWhile (== '+') ys) of
                  Nothing      -> Nothing
                  Just (aa,bb) -> Just (Add aa bb)
     |  elem '-' xs =
         let (front,ys) = span (/= '-') xs  in
             if null front then
                 case (parseString $ dropWhile (== '-') ys) of
                    Just (Value n)         -> Just $ Value (-1 * n)
                    Just (Cval  n bb)      -> Just $ Cval (-1 * n) bb 
                    _                      ->  Nothing          
             else 
                 case maybe2 (parseString front) (parseString $ dropWhile (== '-') ys) of
                    Nothing      -> Nothing
                    Just (aa,bb) -> Just (Sub aa bb) 
     |  elem '/' xs = 
         let (front,ys) = span (/= '/') xs  in
             case maybe2 (parseString front) (parseString $ dropWhile (== '/') ys) of
                  Just (Value aa, Value bb) -> Just (Div  (Value aa) (Value bb))
                  _                         -> Nothing
     | any (== 'x') xs  =   
         let (front,back)  = span isNumber xs in
             case back of 
                 "x"      -> if null front then 
                                Just Var 
                             else if (all isNumber front) then
                                Just $ Cval (read front) Var
                             else Nothing
                 _        -> Nothing 
     | otherwise  =  Nothing


--parseString' = liftM group . parseString
-- such strings
switchY b x xs   = if b then  (x : xs) else "y"
plusMinus :: Bool ->  String -> String
plusMinus   _   ""           = ""
plusMinus   b ('+':'-':xs)   = switchY b '-' $ plusMinus b xs
plusMinus   b ('-':'+':xs)   = switchY b '-' []
plusMinus   b ('-':'-':xs)   = switchY False '+' []
plusMinus   b ('+':'+':xs)   = switchY False '+' []
plusMinus   b (x:xs)         = x : plusMinus b xs  
        
-- applying the parser to a string
parseResult :: (Expr -> Expr) -> String -> Either String String
parseResult f str = 
    case (liftM f . parseString .  plusMinus False . filter (not . isSpace)) str of
      Nothing -> Right "Invalid string entered. "
      Just eq -> Left   $ display  eq 
--------------------------------------------------------------------------

-- equations are pairs of expressions representing LHS and RHS
data Equation = Eqn Expr Expr 

instance Show Equation where
    show (Eqn a b) = show a ++" = "++ show b

-- parsing equations: parse the lhs and rhs using parsesString above. 
parseEqString :: String -> Maybe Equation
parseEqString  str  
     | not (elem '=' str)     = Nothing 
     | otherwise              =
         let (lhs,rhs) = span (/= '=')  $ filter (not . isSpace) str 
         in     liftM (uncurry Eqn) $ maybe2 (parseString lhs) (parseString $ dropWhile (== '=') rhs) 

--- is equation expressed as a solution
solved :: Equation -> Bool
solved (Eqn Var (Value _))                 = True
solved (Eqn Var (Div (Value _) (Value _))) = True
solved        _                            = False

--- rules for division
divide :: Equation -> Equation
divide l@(Eqn (Cval n Var) (Value m))                 
    | n < 0 && m < 0                                =  Eqn Var (Div (Value (-m)) (Value (-n)))
    | n < 0                                         =  Eqn Var (Div (Value (-m)) (Value (-n)))
    | m == 0                                        =  if n /= 0 then (Eqn Var (Value 0)) else l
    | m == n                                        =  (Eqn Var (Value 1))
    | n == 1                                        =  (Eqn Var (Value m))                                               
    | otherwise                                     =  Eqn Var (Div (Value m) (Value n))
divide (Eqn (Cval n Var) (Div (Value m) (Value o))) =  Eqn Var (Div (Value m) (Value $ o * m))
divide       eq                                     =  eq

-- can div
canDiv :: Equation -> Bool
canDiv (Eqn (Cval n Var) (Value m))                 =  True
canDiv (Eqn (Cval n Var) (Div (Value m) (Value o))) =  True
canDiv       _                                      =  False


-----
data Loc = WAdd | WSub | Sg deriving (Eq , Show)

-- execute a transposition 
transpose :: Equation -> Equation 
transpose eq@(Eqn el er) =
     case locVar True er of  -- 
        Just (Sg, l) ->   Eqn (simplify $ Sub el l) (simplify $ Sub er l)
        Just (WSub, l) -> Eqn (simplify $ Add l el) (simplify $ Add l er)
        Just (WAdd, l) -> Eqn (simplify $ Sub l el) (simplify $ Sub l er)  
        Nothing ->  case locVar False el of 
                      Just (Sg, l) ->   Eqn (simplify $ Sub el l) (simplify $ Sub er l) 
                      Just (WSub, l) -> Eqn (simplify $ Add l el) (simplify $ Add l er)
                      Just (WAdd, l) -> Eqn (simplify $  Sub l el) (simplify $ Sub er l) 
                      Nothing        -> eq
     where
       --- locating values and variables for transposing
       -- locVar True for variables and locVar False for values
       locVar :: Bool -> Expr -> Maybe (Loc , Expr)
       locVar True Var          = Just (Sg, Var)
       locVar False (Value n)   = Just (Sg, Value n)
       locVar True (Cval n Var) = Just (Sg, Cval n Var)  
       locVar b (Sub l r)       = 
                     case (locVar b l) of
                       Nothing     ->  case locVar b  r of 
                                         Just (sg, ys) ->  if sg == Sg then
                                                               Just (WSub, ys)
                                                           else 
                                                               Just (sg, ys)
                                         _     -> Nothing 
                       Just (sg, ys) -> if sg == Sg then
                                            Just (WAdd, ys)
                                        else 
                                            Just (sg, ys)
       locVar b (Add l r)       = 
                    case (locVar b l) of
                       Nothing     ->  case locVar b r of 
                                         Just (sg, ys) ->  if sg == Sg then
                                                               Just (WAdd, ys)
                                                           else 
                                                               Just (sg, ys)
                                         _     -> Nothing 
                       Just (sg, ys) -> if sg == Sg then
                                            Just (WAdd, ys)
                                        else 
                                            Just (sg, ys)
       locVar  _   _            =  Nothing

-------------------------------------------------------------------------------------------
---------------------- solving an equation -----------------------
-- we generate a list of steps taken to solve the equation, so we can easily trace the
-- steps by printing out the list
solveEqnl :: Equation -> [(Equation, String)]
solveEqnl eq@(Eqn Var (Div _ (Value 0)))  = [(eq,"undefined")] 
solveEqnl eqn 
    | solved eqn    = [] 
    | canDiv eqn    = let deqn = divide eqn in  [(deqn,"Dividing")] ++ solveEqnl deqn 
    | canTrans eqn  = let teqn = transpose eqn in [(teqn,"Transposing") ] ++ solveEqnl teqn 
    | otherwise     =  case appAddSub eqn of
                         (eq , Nothing) -> solveEqnl eq
                         (eq, Just str) -> [(eq,str)] ++  solveEqnl eq 
        where 
           --
           addEq :: Equation -> Equation
           addEq (Eqn a b)  =  Eqn (add a) (add b)
           --
           subEq :: Equation -> Equation
           subEq (Eqn a b) = Eqn (sub a) (sub b)
           --
           sEnEql :: Equation -> Equation -> Bool
           sEnEql (Eqn el er) (Eqn ea eb) = sEqual el ea && sEqual er eb 
           --
           canTrans :: Equation -> Bool
           canTrans (Eqn el er)  = isDVal el || isDVar er
                   where
                       isDVal , isDVar :: Expr -> Bool
                       isDVal (Sub l r) = isDVal l || isDVal r
                       isDVal (Add l r) = isDVal l || isDVal r
                       isDVal      ex   = isVal ex 
                       --
                       isDVar (Sub l r) = isDVar l || isDVar r
                       isDVar (Add l r) = isDVar l || isDVar r
                       isDVar      ex   = isVar ex  
           ---
           appAddSub :: Equation -> (Equation, Maybe String)
           appAddSub eqn = 
                let aeqn = addEq eqn 
                    seqn = subEq eqn 
                in 
                    if sEnEql eqn aeqn then 
                        if sEnEql eqn seqn then 
                            (eqn , Nothing)
                        else (seqn , Just "Subtracting")
                    else 
                        (aeqn, Just "Adding")

--- solving equation from an input string
runSolvr :: String -> IO ()
runSolvr   str = do 
     let ms =  liftM solveEqnl $ parseEqString str
     case ms of   
        -- we use take 15 here for debugging reasons, in case we end up with an infininte loop 
        Just xs  -> mapM_ (\(a,b) ->putStrLn (show a ++ " " ++ b)) $ take 15 xs
        Nothing  -> print "error in input" 

main                 :: IO ()
main                  = do 
                           putStr "\ESC[2J"
                           putStr "\ESC[0;0H"
                           putStrLn " SIMPLE EQUATION SOLVER (solves equations like: ax + b = cx + d)"
                           let str1 = "\nEnter the equation to solve : "
                           let str2 =  "-----------------------------------------------------------------"         
                           putStrLn (str2 ++ str1)
                           str <- getLine
                           runSolvr str
