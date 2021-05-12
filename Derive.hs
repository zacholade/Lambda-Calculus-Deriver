
--------------------------------------------
--                                        --
-- CM20256/CM50262 Functional Programming --
--                                        --
--         Coursework 2020/2021           --
--                                        --
--------------------------------------------



------------------------- Auxiliary functions

find :: (Show a,Eq a) => a -> [(a,b)] -> b
find x [] = error ("find: " ++ show x ++ " not found")
find x ((y,z):zs)
  | x == y    = z
  | otherwise = find x zs


merge :: Ord a => [a] -> [a] -> [a]
merge xs [] = xs
merge [] ys = ys
merge (x:xs) (y:ys)
    | x == y    = x : merge xs ys
    | x <= y    = x : merge xs (y:ys)
    | otherwise = y : merge (x:xs) ys

minus :: Ord a => [a] -> [a] -> [a]
minus xs [] = xs
minus [] ys = []
minus (x:xs) (y:ys)
    | x <  y    = x : minus    xs (y:ys)
    | x == y    =     minus    xs    ys
    | otherwise =     minus (x:xs)   ys


------------------------- Lambda-terms

type Var = String

data Term =
    Variable Var
  | Lambda   Var  Term
  | Apply    Term Term
  deriving Eq


instance Show Term where
  show = f 0
    where
      f i (Variable x) = x
      f i (Lambda x m) = if i /= 0 then "(" ++ s ++ ")" else s where s = "\\" ++ x ++ ". " ++ f 0 m 
      f i (Apply  n m) = if i == 2 then "(" ++ s ++ ")" else s where s = f 1 n ++ " " ++ f 2 m

free :: Term -> [Var]
free (Variable x) = [x]
free (Lambda x n) = free n `minus` [x]
free (Apply  n m) = free n `merge` free m


------------------------- Types

infixr 5 :->

type Atom = String
data Type = At Atom | Type :-> Type
  deriving Eq

instance Show Type where
  show (At a)       = a
  show (At a :-> s) = a ++ " -> " ++ show s
  show    (t :-> s) = "(" ++ show t ++ ") -> " ++ show s


atoms :: [Atom]
atoms = map (:[]) ['a'..'z'] ++ [ a : show i | i <- [1..], a <- ['a'..'z'] ]

t1 :: Type
t1 = At "a" :-> At "b"

t2 :: Type
t2 = (At "c" :-> At "d") :-> At "e"

t3 :: Type
t3 = At "a" :-> At "c" :-> At "c"

t4 :: Type
t4 = (At "o" :-> At "d") :-> At "e"

t5 :: Type
t5 = At "p"

t6 :: Type
t6 = At "a" :-> At "a" :-> At "b"

t7 :: Type
t7 = At "s" :-> t4 :-> t1


------------------------- Assignment 1

occurs :: Atom -> Type -> Bool
occurs a (At x)    = a == x
occurs a (x :-> y) = occurs a x || occurs a y


findAtoms :: Type -> [Atom]
findAtoms (At x)    = [x]
findAtoms (x :-> y) = (findAtoms x) `merge` (findAtoms y)


------------------------- Type substitution

type Sub = (Atom,Type)

s1 :: Sub
s1 = ("a", At "e")

s2 :: Sub
s2 = ("e", At "b" :-> At "c")

s3 :: Sub
s3 = ("c", At "a" :-> At "a")

s4 :: Sub
s4 = ("a", At "d")


------------------------- Assignment 2

sub :: Sub -> Type -> Type
sub (a, b) (At x)    = if x == a then b else (At x)
sub (a, b) (x :-> z) = sub (a, b) x :-> sub (a, b) z

subs :: [Sub] -> Type -> Type
subs [] t     = t
subs (x:xs) t = sub x (subs xs t)

------------------------- Unification

type Upair = (Type,Type)
type State = ([Sub],[Upair])
-- State = ([Atom, Type],[Type, Type])

u1 :: Upair
u1 = (t1,At "c")

u2 :: Upair
u2 = (At "a" :-> At "a",At "a" :-> At "c")

u3 :: Upair
u3 = (t1,t2)

u4 :: Upair
u4 = (t2,t3)

st1 :: State
st1 = ([],[u1,u2])


------------------------- Assignment 3


sub_u :: Sub -> [Upair] -> [Upair]
sub_u _ [] = []
sub_u s ((t1, t2):xs) = (sub s t1, sub s t2) : (sub_u s xs)


step :: State -> State
step (s, (At(x1), At(x2)):ys ) | x1 == x2         = (s, ys)
step (s, (At(x1), x2):ys)                         = if x1 `occurs` x2 then error "Step: atom a occurs in a -> b." else (([(x1, x2)] ++ s), sub_u (x1, x2) ys)
step (s, (x1, At(x2)):ys)                         = if x2 `occurs` x1 then error "Step: atom a occurs in a -> b." else (([(x2, x1)] ++ s), sub_u (x2, x1) ys)
step (s, (left1 :-> right1, left2 :-> right2):ys) = (s, (left1, left2) : (right1, right2) : ys)


unify :: [Upair] -> [Sub]
unify [] = []
unify xs = fst (run ([], xs))
  where
    run :: State -> State
    run (xs, []) = (xs, [])
    run (xs, ys) = run (step (xs, ys))


------------------------- Assignment 4

type Context   = [(Var, Type)]
type Judgement = (Context, Term, Type)

data Derivation =
    Axiom       Judgement
  | Abstraction Judgement Derivation
  | Application Judgement Derivation Derivation


d1 = Application ([("y",At "a")], n1 , At "a") (
       Abstraction ([("y",At "a")],Lambda "x" (Variable "x"),At "a" :-> At "a") (
         Axiom ([("x",At "a"),("y",At "a")],Variable "x",At "a")
     ) ) (
       Axiom ([("y",At "a")], Variable "y", At "a")
     )

d2 = Application ([("y",At "b")],Apply (Lambda "x" (Apply (Variable "x") (Variable "y"))) (Lambda "z" (Variable "z")),At "a") (
       Abstraction ([("y",At "b")],Lambda "x" (Apply (Variable "x") (Variable "y")),At "c") (
         Application ([("x",At "d"),("y",At "b")],Apply (Variable "x") (Variable "y"),At "e") (
           Axiom ([("x",At "d"),("y",At "b")],Variable "x",At "f")
         ) (
           Axiom ([("x",At "d"),("y",At "b")],Variable "y",At "g")
     ) ) ) (
       Abstraction ([("y",At "b")],Lambda "z" (Variable "z"),At "h") (
         Axiom ([("z",At "i"),("y",At "b")],Variable "z",At "j")
     ) )


conclusion :: Derivation -> Judgement
conclusion (Axiom j)           = j
conclusion (Abstraction j d)   = j
conclusion (Application j d e) = j


subs_ctx :: [Sub] -> Context -> Context
subs_ctx [] c               = c
subs_ctx _ []               = []
subs_ctx s ((v, t):ys)      = (v, subs s t) : subs_ctx s ys


subs_jdg :: [Sub] -> Judgement -> Judgement
subs_jdg [] j        = j
subs_jdg s (c, t, y) = (subs_ctx s c, t, subs s y)


subs_der :: [Sub] -> Derivation -> Derivation
subs_der [] d                  = d
subs_der s (Axiom j)           = Axiom (subs_jdg s j)
subs_der s (Abstraction j d)   = Abstraction (subs_jdg s j) (subs_der s d)
subs_der s (Application j d e) = Application (subs_jdg s j) (subs_der s d) (subs_der s e)



------------------------- Typesetting derivations


instance Show Derivation where
  show d = unlines (reverse strs)
    where
      (_,_,_,strs) = showD d

      showC :: Context -> String
      showC [] = []
      showC [(x,t)]    = x ++ ": " ++ show t
      showC ((x,t):cx) = x ++ ": " ++ show t  ++ " , " ++ showC cx

      showJ :: Judgement -> String
      showJ ([],n,t) =              "|- " ++ show n ++ " : " ++ show t
      showJ (cx,n,t) = showC cx ++ " |- " ++ show n ++ " : " ++ show t

      showL :: Int -> Int -> Int -> String
      showL l m r = replicate l ' ' ++ replicate m '-' ++ replicate r ' '

      showD :: Derivation -> (Int,Int,Int,[String])
      showD (Axiom j) = (0,k,0,[s,showL 0 k 0]) where s = showJ j; k = length s
      showD (Abstraction j d)   = addrule (showJ j) (showD d)
      showD (Application j d e) = addrule (showJ j) (sidebyside (showD d) (showD e))

      addrule :: String -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      addrule x (l,m,r,xs)
        | k <= m     = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL  l m r  : xs)
        | k <= l+m+r = (ll,k,rr, (replicate ll ' ' ++ x ++ replicate rr ' ') : showL ll k rr : xs)
        | otherwise  = (0,k,0, x : replicate k '-' : [ replicate (-ll) ' ' ++ y ++ replicate (-rr) ' ' | y <- xs])
        where
          k = length x
          i = div (m - k) 2
          ll = l+i
          rr = r+m-k-i

      extend :: Int -> [String] -> [String]
      extend i strs = strs ++ repeat (replicate i ' ')

      sidebyside :: (Int,Int,Int,[String]) -> (Int,Int,Int,[String]) -> (Int,Int,Int,[String])
      sidebyside (l1,m1,r1,d1) (l2,m2,r2,d2)
        | length d1 > length d2 = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip d1 (extend (l2+m2+r2) d2)])
        | otherwise             = ( l1 , m1+r1+2+l2+m2 , r2 , [ x ++ "  " ++ y | (x,y) <- zip (extend (l1+m1+r1) d1) d2])



------------------------- Assignment 5


n  = Lambda "x" (Lambda "y" (Lambda "z" (Apply(Apply(Variable "x")(Variable "z"))(Apply(Variable "y")(Variable "z")))))
n0 = Lambda "x" (Lambda "x" (Variable "x"))
n1 = Apply (Lambda "x" (Variable "x")) (Variable "y")
n2 = Lambda "x" (Apply (Variable "x") (Variable "y"))
n3 = Lambda "x" (Apply (Apply (Variable "x") (Variable "y")) (Variable "y"))
n4 = Apply (Apply (Lambda "x" (Variable "x")) (Variable "y")) (Variable "z")
n5 = Apply (Variable "x") (Variable "y")

-- q1 = Lambda "f" (Lambda "g" (Lambda "x" (Apply (Variable "g") Apply((Apply (Variable "f") (Variable "x"))(Variable "x")))))

m1 = Lambda "f" (Lambda "g" (Lambda "x" (Apply (Variable "g") (Apply (Apply (Variable "f") (Variable "x")) (Variable "x")))))
x1 = Lambda "x" (Lambda "y" (Variable "x"))
m1x1 = Apply m1 x1
x2 = Lambda "w" (Variable "w")
m1x1x2 = Apply m1x1 x2


derive0 :: Term -> Derivation
derive0 t =
  let j = (makeContext t, t, At(""))
    in
      aux j
      where
        aux :: Judgement -> Derivation
        aux (c, (Variable term), typee)   = Axiom       (c, (Variable term), typee)
        aux (c, (Apply t1 t2), typee)     = Application (c, (Apply t1 t2), typee) (aux (c, t1, typee)) (aux (c, t2, typee))
        aux (c, (Lambda var term), typee) = Abstraction (c, (Lambda var term), typee) (aux ((updateContext var c), term, At("")))

        makeContext :: Term -> Context
        makeContext t  = [(freev, At("")) | freev <- (free t)]

        updateContext :: Var -> Context -> Context
        updateContext nv c  = if nv `elem` [fst c | c <- c] then c else (nv, At("")) : c


derive1 :: Term -> Derivation
derive1 t =
  let (atom:xs)     = atoms
      (cTypes, xs') = popn (length (free t)) xs
    in
      aux xs' ((zip (free t) [At(t') | t' <- cTypes]), t, At(atom))
  where
    aux :: [Atom] -> Judgement -> Derivation
    aux _          (c, (Variable term), typee)   = Axiom       (c, (Variable term), typee)
    aux (a1:a2:xs) (c, (Apply t1 t2), typee)     = Application (c, (Apply t1 t2), typee) (aux (odds xs) (c, t1, At(a1))) (aux (evens xs) (c, t2, At(a2)))
    aux (a1:a2:xs) (c, (Lambda var term), typee) = Abstraction (c, (Lambda var term), typee) (aux xs ((updateContext var a1 c, term, At(a2))))
  
    -- Returns tuple of ([Atoms popped off], [Atom Supply])
    popn :: Int -> [Atom] -> ([Atom], [Atom])
    popn n xs = drop' n xs [] 
      where
        drop' :: Int -> [Atom] -> [Atom] -> ([Atom], [Atom])
        drop' 0 xs ys     = (ys, xs)
        drop' n (x:xs) ys = drop' (n-1) (xs) ((x):ys)

    evens :: [a] -> [a]
    evens (x:xs) = x:odds xs
    evens _      = []

    odds :: [a] -> [a]
    odds (_:xs) = evens xs
    odds _      = []

    updateContext :: Var -> Atom -> Context -> Context
    -- Check if the elem is already in the context. If so then as per the spec, we need to REPLACE the old occurrance with new type (then block).
    -- Otherwise we replace the previous context with the new context tuple appended (else block)
    updateContext nv a c  = if nv `elem` [fst c | c <- c] then (nv, At(a)):[(v, t) | (v, t) <- c, v /= nv] else (nv, At(a)) : c


upairs :: Derivation -> [Upair]
upairs d = aux d []
  where 
    aux :: Derivation -> [Upair] -> [Upair]
    aux (Axiom       (ctx, (Variable v), typee))        up = (typee, (getVarTypeFromContext v (Axiom (ctx, (Variable v), typee)))):up
    aux (Abstraction (ctx, (Lambda v t), typee) d)      up = (typee, ((getVarTypeFromContext v d) :-> (getTermType d))):(aux d up)
    aux (Application (ctx, (Apply t1 t2), typee) d1 d2) up = ((getTermType d1), ((getTermType d2) :-> typee)):(aux d1 up ++ aux d2 up)

    getTermType :: Derivation -> Type
    getTermType (Axiom       (ctx, t, typee)    ) = typee    
    getTermType (Abstraction (ctx, t, typee) _  ) = typee
    getTermType (Application (ctx, t, typee) _ _) = typee

    getVarTypeFromContext :: Var -> Derivation -> Type
    getVarTypeFromContext v (Axiom       (ctx, t, typee)    ) = varMatcher v ctx
    getVarTypeFromContext v (Abstraction (ctx, t, typee) _  ) = varMatcher v ctx
    getVarTypeFromContext v (Application (ctx, t, typee) _ _) = varMatcher v ctx

    varMatcher :: Var -> Context -> Type
    varMatcher vToFind []          = error "The variable isn't in context for some reason?! Derivation not formatted correctly..."
    varMatcher vToFind ((v, t):xs) = if v == vToFind then t else varMatcher vToFind xs   

derive :: Term -> Derivation
derive t = subs_der (unify . upairs . derive1 $ t) (derive1 t)