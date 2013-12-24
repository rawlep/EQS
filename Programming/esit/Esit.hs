module Esit (parseResult, group, eEqual, add, sub) where

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

-- if the expression has a variable
isVar :: Expr -> Bool
isVar Var          = True
isVar (Cval _ Var) = True
--isVar (Add l r)    = isVar l && isVar r
--isVar (Sub l r)    = isVar l && isVar r
--isVar (Div l r)    = isVar l && isVar r
isVar    x         = False


-- if the expression has a value
isVal :: Expr -> Bool
isVal (Value _)    = True
isVal _            = False

canComp :: Expr -> Expr -> Bool
canComp  l r = (isVar l && isVar r) || (isVal l && isVal r)

-- vlaidating expressions --- do i need this?
isValid :: Expr -> Bool
isValid Var                       = True
isValid (Cval _ Var)              = True
isValid (Cval _ _)                = False
isValid (Value _)                 = True
isValid (Div (Value _) (Value _)) = True
isValid (Div _ _)                 = False
isValid (Add l r)                 = isValid l && isValid r
isValid (Sub l r)                 = isValid l && isValid r 

-- sytactic equality fro comaparing operations
sEqual :: Expr -> Expr -> Bool
sEqual Var        Var             = True
sEqual (Value n) (Value m)        = m == n
sEqual (Cval n l) (Cval m r)      = n == m && sEqual l r
sEqual (Add l r) (Add ll rr)      = sEqual l ll && sEqual r rr
sEqual (Sub l r) (Sub ll rr)      = sEqual l ll && sEqual r rr
sEqual (Div a b) (Div c d)        = sEqual a c  && sEqual c b
sEqual    _         _             = False

-------------------------------------------------------------------------
--- Arithmetic operations
-------------------------------------------------------------------------
-- grouping
group :: Expr -> Expr
group (Add (Sub a b) (Add c d))               
    | isVar c                                 = Add c (group $ Add (Sub a b) d)
    | isVal c                                 = Add (group $ Add (Sub a b) d) c
    | otherwise                               = Sub (group $ Add (Add a c) d) b
group (Sub (Add a b) (Sub c d))               = Add (group $ Sub a c) (group $ Sub b d)
group (Add (Add l ll) r)      
    | canComp l r  && (not $ isVar ll)        = Add (Add l r) ll
    | canComp l r  && (not $ isVal ll)        = Add (Add l r) ll
    | otherwise                               = Add  l (group $ Add ll  r)      
group  (Add l (Add ll r))                     = group $ Add (Add l ll) r
--
group (Sub l (Sub ll r))       
    | canComp l r  && (not $ isVar ll)        =  Sub (Sub l r) ll
    | canComp l r  && (not $ isVal ll)        =  Sub (Sub l r) ll
    | otherwise                               =  Sub  l (group $ Sub ll  r)   
--
group (Sub (Sub l  ll) r)                     = group (Sub l (Sub ll r)) 
--
group (Add (Sub l  ll) r)                     -- = Sub (Add l r) ll   
    | canComp l r  && (not $ isVar ll)        =  Sub (Add l r) ll
    | canComp l r  && (not $ isVal ll)        =  Sub (Add l r) ll
    | otherwise                               =  Sub (Add l r) ll                 
-- add sub
group (Add l (Sub ll r))                      =  Add (Sub l r) ll  
group (Sub l (Add ll r))                      =  Sub (Add  l r) ll 
group (Sub l r)                               =  Sub (group l) (group r)
group (Add l r)                               =  Add (group l) (group r) 
group  xs                                     =  xs

-- adding
add :: Expr -> Expr 
add (Add Var Var)                        = Cval 2 Var
add (Add (Value n)  (Value m))           = Value (n+m)
add (Add (Cval n Var)  (Cval m Var))     = Cval (n+m) Var
add (Add Var (Cval n Var))   
    | n == 0                             = Var
    | otherwise                          = Cval (n+1) Var 
add (Add (Cval n Var) Var)   
    | n == 0                             = Var
    | otherwise                          = Cval (n+1) Var 
add (Add l (Add r k))                    
    | canComp l r                        =  Add (add $ Add l r) k
    | canComp l k                        =  Add r (add $ Add l k)        
    | otherwise                          =  Add l (add $ Add  r k)
add (Add (Add l  r) k)                   =  add $ Add l (Add  r k)
-- add sub
add (Add l (Sub ll r))                   =  Sub (add (Add l ll)) r 
add (Sub l (Add ll r))                   =  Sub l (add (Add ll r)) 
add (Sub (Add l ll) r)                   =  Sub (add $ Add l ll) r
add (Add (Sub l  r) k)                  
    | canComp k  r                       =  Sub l (add $ Add r k) 
    | canComp l  k                       =  Sub  (add $ Add l k) r           
    | otherwise                          =  Add (add $ Sub  l r) k
add (Sub l r)                            =  Sub (add l) (add r)
add (Add l r)                            =  Add (add l) (add r)
add  xs                                  =  xs

--subtracting
sub :: Expr -> Expr
sub (Sub l (Sub (Value n) (Value m)))   = Sub l (Value (n + m))
sub (Sub l (Sub (Cval  n Var) (Cval m Var)))   = Sub l (Cval (n + m) Var)
sub (Sub Var Var)                       = Value 0
sub (Sub (Value n) (Value m))           = Value (n-m)
sub (Sub (Cval n Var)  (Cval m Var))    = Cval (n-m) Var
sub (Sub Var (Cval n Var))   
    | n == 1                            = Value 0
    | otherwise                         = Cval (1 - n) Var
sub (Sub (Cval n Var) Var)   
    | n == 1                            = Value 0
    | otherwise                         = Cval (n-1) Var
-- sub sub
{--sub  (Sub l (Sub (Value n)  (Value m)))
--     | n 
sub  (Sub l (Sub r k))  -- (Sub l (Sub r (sub p e)))         
    | canComp r   k                     = Sub l (sub $ Sub  r k) 
    | canComp l  r  && (not $ isVar k)  =  Sub (sub $ Sub l r) k 
    | canComp l  r  && (not $ isVal k)  =  Sub (sub $ Sub l r) k
    | otherwise                         =  Sub (Sub  l r) (sub k)
sub   (Sub (Sub l  r) k)                =  Sub l (sub $ Sub r  k)
--}
sub (Sub l (Add k r))                  
    | canComp l k                      =  Add (sub $ Sub l k) r  
    | canComp k  r  && (not $ isVar l) =  Sub l (add $ Add  r k)
    | canComp k  r  && (not $ isVal l) =  Sub l (add $ Add  r k)
    | otherwise                        =  Sub l (sub $ Add k r)
--
sub (Add l (Sub r k))                   = Add (sub l) (sub $ Sub r k)
sub (Add (Sub l  r) k)                  = Add (sub $ Sub l r) (sub k)
sub (Sub (Add l  r) k)                 -- = Add l (sub $ Sub r k)
    | canComp l  k  && (not $ isVar r)  =  Add (sub $ Sub l k) r
    | canComp l  k  && (not $ isVal r)  =  Add (sub $ Sub l k) r
    | canComp r  k  && (not $ isVar l)  =  Add l (sub $ Sub r k) 
    | canComp r  k  && (not $ isVal l)  =  Add l (sub $ Sub r k) 
    | otherwise                         =  Sub (sub $ Add l r) (sub k)
sub (Add  l  r)                         = Add (sub l) (sub r)
sub (Sub  l  r)                         = Sub (sub l) (sub r)
--
sub   xs                                =  xs 


--- simplify
-- need to write a function to negate additions/substractions like ax+6+4x+7
simplify  = simplify' 1 -- :: Int -> Expr -> Expr
simplify' :: Int -> Expr -> Expr
simplify' n ex
    | normFrm ex    = ex
    | n > 200       = ex                  
   -- | canSub  ex    = simplify' (n + 1) $ sub ex   
   -- | canAdd  ex    = simplify' (n + 1) $ add ex               
    | otherwise     = simplify' (n + 1) $ appOrGroup (sub . add) ex 
    where 
      appOrGroup :: (Expr -> Expr) -> Expr -> Expr
      appOrGroup  f   ex   = let fex = f ex in 
                               if  sEqual (f ex) ex then group ex else fex
      -- can add
      canAdd :: Expr -> Bool
      canAdd  (Add Var Var)  = True
      canAdd  (Add (Value _)  (Value _))  = True
      canAdd  (Add (Cval _ Var)  (Cval _ Var))     = True
      canAdd  (Add Var (Cval _ Var))                = True   
      canAdd  (Add (Cval n Var) Var) = True
      canAdd  (Add (Cval _ Var) (Add (Cval _ Var) _))  = True 
      canAdd  (Add (Value _) (Add (Value _) _)) = True
      canAdd  (Add (Cval _ Var) (Add  Var _))  = True 
      canAdd  (Add  Var (Add (Cval _ Var) _)) = True
      canAdd  (Add  Var (Add  Var _)) = True
      canAdd  (Sub l r)              = any (== True) [canAdd l , canAdd r]
      canAdd  (Add l r)              = any (== True) [canAdd l , canAdd r]
      canAdd    _                    = False
       -- can Sub
      canSub :: Expr -> Bool
      canSub  (Sub Var Var)  = True
      canSub  (Sub (Value _)  (Value _))  = True
      canSub  (Sub (Cval _ Var)  (Cval _ Var))     = True
      canSub  (Sub Var (Cval _ Var))                = True   
      canSub  (Sub (Cval _ Var) Var) = True
      canSub  (Sub (Cval _ Var) (Sub (Cval _ Var) _))  = True 
      canSub  (Sub (Value _) (Sub (Value _) _)) = True
      canSub  (Sub (Cval _ Var) (Sub  Var _))  = True 
      canSub  (Sub  Var (Sub (Cval _ Var) _)) = True
      canSub  (Sub  Var (Sub  Var _)) = True
      canSub  (Sub l r)              = canSub l || canSub r
      canSub  (Add l r)              = canSub l || canSub r
      canSub    _                    = False
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
-- the parser  would validate strings like "3+_5" so need to preprocess
-- such strings
switchY b x xs   = if b then  (x : xs) else "y"
plusMinus :: Bool ->  String -> String
plusMinus   _   ""           = ""
plusMinus   b ('+':'-':xs)   = switchY b '-' $ plusMinus b xs
plusMinus   b ('-':'+':xs)   = switchY b '-' []
plusMinus   b ('-':'-':xs)   = switchY False '+' []
plusMinus   b ('+':'+':xs)   = switchY False '+' []
plusMinus   b (x:xs)         = x : plusMinus b xs  
--      where        
-- applying the parser to a string
parseResult :: (Expr -> Expr) -> String -> Either String String
parseResult f str = 
    case (liftM f . parseString .  plusMinus False . filter (not . isSpace)) str of
      Nothing -> Right "Invalid string entered. "
      Just eq -> Left   $ display  eq -- . plusMinus True
--------------------------------------------------------------------------

data Loc = WAdd | WSub | Sg deriving Eq

locVar :: Expr -> Maybe (Loc , Expr)
locVar Var          = Just (Sg, Var)
locVar (Cval n Var) = Just (Sg, Cval n Var) 
locVar (Add l r)    = case (locVar l) of
                       Nothing     ->  case locVar r of 
                                         Just (sg, ys) ->  if sg == Sg then
                                                               Just (WAdd, ys)
                                                           else 
                                                               Just (sg, ys)
                                         _     -> Nothing 
                       Just (sg, ys) -> if sg == Sg then
                                            Just (WAdd, ys)
                                        else 
                                            Just (sg, ys)
locVar (Sub l r)    = case (locVar l) of
                       Nothing     ->  case locVar r of 
                                         Just (sg, ys) ->  if sg == Sg then
                                                               Just (WSub, ys)
                                                           else 
                                                               Just (sg, ys)
                                         _     -> Nothing 
                       Just (sg, ys) -> if sg == Sg then
                                            Just (WSub, ys)
                                        else 
                                            Just (sg, ys)
locVar    x         = Nothing

-- locate the value
locVal :: Expr -> Maybe (Loc , Expr)
locVal (Value n)    = Just (Sg, Value n)
locVal (Add l r)    = case (locVal l) of
                       Nothing     ->  case locVal r of 
                                         Just (sg, ys) ->  if sg == Sg then
                                                               Just (WAdd, ys)
                                                           else 
                                                               Just (sg, ys)
                                         _     -> Nothing 
                       Just (sg, ys) -> if sg == Sg then
                                            Just (WAdd, ys)
                                        else 
                                            Just (sg, ys)
locVal (Sub l r)    = case (locVar l) of
                       Nothing     ->  case locVal r of 
                                         Just (sg, ys) ->  if sg == Sg then
                                                               Just (WSub, ys)
                                                           else 
                                                               Just (sg, ys)
                                         _     -> Nothing 
                       Just (sg, ys) -> if sg == Sg then
                                            Just (WSub, ys)
                                        else 
                                            Just (sg, ys)
locVal    x         = Nothing
---------
-- equations 
data Equation = Eqn Expr Expr 

instance Show Equation where
    show (Eqn a b) = show a ++" = "++ show b

-- parsing equations
parseEqString :: String -> Maybe Equation
parseEqString  str  = 
     let (lhs,rhs) = span (/= '=')  str  in
        liftM (uncurry Eqn) $ maybe2 (parseString lhs) (parseString $ dropWhile (== '=') rhs) 

solved :: Equation -> Bool
solved (Eqn Var (Value _))                 = True
solved (Eqn Var (Div (Value _) (Value _))) = True
solved        _                            = False
---
divide :: Equation -> Equation
divide (Eqn (Cval n Var) (Value m))                 =  Eqn Var (Div (Value m) (Value n))
divide (Eqn (Cval n Var) (Div (Value m) (Value o))) =  Eqn Var (Div (Value m) (Value $ o * m))
divide       eq                                     =  eq

 
transpose :: Equation -> Equation 
transpose (Eqn el er) =
     case locVar er of 
        Just (Sg, l) ->   Eqn (Sub el l) (simplify $ Sub er l)
        Just (WSub, l) -> Eqn (Add el l) (simplify $ Add el l)
        Just (WAdd, l) -> Eqn (Sub el l) (simplify $ Sub er l)  
        Nothing ->  case locVal el of 
                      Just (Sg, l) ->   Eqn (simplify $ Sub el l) (Sub er l)
                      Just (WSub, l) -> Eqn (simplify $ Add el l) (Add el l)
                      Just (WAdd, l) -> Eqn (simplify $ Sub el l) (Sub er l) 
                      Nothing        -> Eqn el er