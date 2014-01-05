--
--module esit where

import Data.Char (isNumber,isSpace)
import Data.List (partition)
import Control.Monad (liftM,liftM2)


--- maybe2: returns Just if both maybes are a Just or nothing otherwise
maybe2 :: Maybe a -> Maybe b -> Maybe (a,b)
maybe2 =  liftM2 (,)

--- expressions 
data Expr  =  Var | Value Int | Cval Int Expr | 
              Add Expr Expr | Sub Expr Expr |
              Div Expr Expr   -- deriving Show 

--- displaying equations
display :: Expr -> String
display Var       =  "x"
display (Value n) = show n
display (Cval n e) = show n ++ display e
display (Add (Add k j@(Value n)) r) 
    | n < 0      =          display k ++  display (Add j r)
    | otherwise  =  display k ++ "+" ++  display (Add j r) 
display (Add l r@(Value n)) 
    | n < 0     = display l ++  display r
    | otherwise = display l ++ "+" ++ display r
display (Add l r@(Cval n _))
    | n < 0     = display l ++  display r
    | otherwise = display l ++ "+" ++ display r
display (Add l r@(Add x@(Value n) _)) 
    | n < 0       = display l  ++ display r
    | otherwise   = display l ++ "+" ++ display r
display (Add l r@(Add x@(Cval n _) _)) 
    | n < 0       = display l  ++ display r
    | otherwise   = display l ++ "+" ++ display r
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

-- we do not really need subtraction, since we can always
-- normalise subtractions to additions
sub2add :: Expr -> Expr
sub2add  (Sub (Add l r) k)            = Add (sub2add l) (Add (sub2add r) (sub2add k))
sub2add  (Sub (Sub l r) k)            = Add (sub2add l) (Add (sub2add r) (sub2add k))
sub2add  (Sub l (Value n))            = Add (sub2add l) (Value (-n))
sub2add  (Sub l Var)                  = Add (sub2add l) (Cval (-1) Var)
sub2add  (Sub l (Cval n Var))         = Add (sub2add l) (Cval (-n) Var)
sub2add  (Add l r)                    = Add (sub2add l) (sub2add r)
sub2add  (Sub l (Sub (Value n) k))    = Add (sub2add l) (sub2add $ Sub (Value (-n)) k )
sub2add  (Sub l (Sub (Cval n Var) k)) = Add (sub2add l) (sub2add $ Sub (Cval (-n) Var) k ) 
sub2add  (Sub l r)                    = Add (sub2add l) (sub2add r)
sub2add     xs                        = xs 
--

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
--- rewrite rules for simplification
-------------------------------------------------------------------------
-- grouping brings variables to  the left and pushes constants to the right
group :: Expr -> Expr
group (Add l r)                
    | isVar l   =   Add l (group r)
    | isVar r   =   Add r (group l)
    | isVal r   =   Add (group l) r
    | isVal l   =   Add (group r) l
    | otherwise =
        case l of 
           Add x  k  -> if isVar x  then
                             Add x (group $ Add k r)
                        else if isVar k then  
                            Add k (group $ Add x r)
                        else if isVal x then
                            Add (group $ Add k r) x
                        else if isVal k then
                            Add (group $ Add x r) k
                        else     
                            Add (group r) (group l) -- Add x (group $ Add l r)
           _         -> 
               case r of 
                   Add x  k -> 
                        if isVar x then
                            Add x (group $ Add l k)
                        else if isVar k then
                            Add k (group $ Add l x)
                        else if isVal x then
                            Add (group $ Add k r) x
                        else if isVal k then
                            Add (group $ Add x r) k
                        else 
                            Add (group r) (group l)
                   _        -> Add (group r) (group l)
group k@(Sub l r)           = group $ sub2add k
group xs                    = xs


-- adding
add :: Expr -> Expr 
add (Add (Add l  r) k)                      = add $ Add l (Add r k) 
add (Add l (Add r k))                    
    | canComp l r                           =  Add (add $ Add l r) (add k)
    | canComp l k                           =  Add  r  (add $ Add l k)        
    | otherwise                             =  
        case k of 
          Add x y   -> if canComp l x then 
                           Add (add $ Add l x)  (add $ Add r y)
                       else if canComp l y then 
                           Add (add $ Add l y)  (add $ Add r x)
                       else if canComp y r then 
                           Add (add $ Add r y)  (add $ Add l x)
                       else if canComp x r then 
                           Add (add $ Add r x)  (add $ Add l y)
                       else
                          Add l (add $ Add  r  k)
          _         -> Add l (add $ Add  r  k)
add (Add Var Var)                            = Cval 2 Var
add (Add (Value n)  (Value m))               = Value (n+m)
add (Add (Cval n Var)  (Cval m Var))         = Cval (n+m) Var
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
add (Add l r)                               =  Add (add l) (add r)
add  xs                                     =  xs


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

--- simplify
simplify  = simplify' 1 -- :: Int -> Expr -> Expr
simplify' :: Int -> Expr -> Expr
simplify' n ex
    | normFrm ex    = remZero ex
    | n > 100       = remZero ex                          
    | otherwise     = simplify' (n + 1) $  (add  . trnAdd . group . sub2add . remZero) ex 
    where 
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
      Just eq -> Left   $ show eq 
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
             prString  =   (liftM sub2add) . parseString          
         in     liftM (uncurry Eqn) $ maybe2 (prString lhs) (prString $ dropWhile (== '=') rhs) 

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

-- execute a transposition 
transpose :: Equation -> (Equation,(Equation,String)) 
transpose eq@(Eqn el er) =
     case locVar True er of  -- 
        Just   l      ->  let kl  =  Add el (negV  l) 
                              kr  =  Add er (negV  l)       
                              str =  if isNeg l then  "Adding" else "Subtracting" 
                          in
                             ( Eqn kl  (simplify kr) ,  (Eqn (simplify kl) (simplify kr), str))
        Nothing ->  case locVar False el of 
                      Just    l    ->   let kr  =  Add er (negV  l)
                                            kl  =  Add el (negV  l)       
                                            str =  if isNeg l then  "Adding" else "Subtracting" 
                                        in           
                                           (Eqn (simplify kl) kr , (Eqn (simplify kl) (simplify kr), str))
                      Nothing        -> (eq, (eq,""))
     where
       --- locating values and variables for transposing
       negV :: Expr -> Expr
       negV Var         = Cval (-1) Var
       negV (Cval n a)  = Cval (-n) a
       negV (Value n)   = Value (-n)
       negV    xs       =   xs       
       -- locVar True for variables and locVar False for values
       locVar :: Bool -> Expr -> Maybe Expr
       locVar True Var          = Just Var
       locVar False (Value n)  = Just (Value n)           
       locVar True l@(Cval _ _) = Just  l
       locVar b (Sub l r)       = 
                     case (locVar b l) of
                       Nothing     ->  locVar b  r 
                       xs          ->  xs
       locVar b (Add l r)       = 
                    case (locVar b l) of
                       Nothing     ->  locVar b r 
                       xs          -> xs
       locVar  _   _            =  Nothing

----------------------------------------------------------------------------------------
---------------------- solving an equation -----------------------
-- we generate a list of steps taken to solve the equation, so we can easily trace the
-- steps by printing out the list
solveEqnl :: Equation -> [(Equation, String)]
solveEqnl eq@(Eqn Var (Div _ (Value 0)))  = [(eq,"undefined")] 
solveEqnl eqn 
    | solved eqn    = [] 
    | canDiv eqn    = let deqn = divide eqn in  [(deqn,"Dividing")] ++ solveEqnl deqn 
    | canTrans eqn  = let (aeq, (teqn,str)) = transpose eqn in 
                          [(aeq,"Transposing"),(teqn,str) ] ++ solveEqnl teqn 
    | otherwise     =  case appAddSub eqn of
                         (eq , Nothing) -> solveEqnl eq
                         (eq, Just str) -> [(eq,str)] ++  solveEqnl eq 
        where 
           --
           addEq :: Equation -> Equation
           addEq (Eqn a b)  =  Eqn (add a) (add b)
           --
           subEq :: Equation -> Equation
           subEq (Eqn a b) = Eqn (add $ sub2add a) (add $ sub2add b)
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
                           getLine >>= runSolvr
                           --- try again
                           print "Press enter to try again"
                           c <- getChar 
                           if c == '\n' then main else return ()
