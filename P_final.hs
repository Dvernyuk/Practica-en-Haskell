--Dmytro Vernyuk

rel0 = (R [])
rel1 = (R [(1, 1), (1, 2), (2, 1), (2, 2), (3, 3), (3, 4), (4, 3), (4, 4)])
rel2 = (R [(4, 4), (1, 2), (2, 1),( 1, 1), (2, 2), (3, 3), (4, 3), (3, 4)])
rel3 = (R [(1, 1), (1, 2), (1, 3), (1, 4) , (2, 2), (2, 3), (2, 4) , (3, 3), (3, 4), (4, 4)])
rel4 = (R [(1 ,1), (1, 3), (1, 5), (3, 1), (3, 3), (3, 5), (5, 1), (5, 3), (5, 5), (2, 2), (2, 6), (6, 2), (6, 6), (4, 4)])
rel5 = (R [('a','a'),('b','b'),('c','c'),('d','d'),('a','c'),('c','a'),('b','d'),('d','b')])

data Rel a = R [(a,a)] deriving (Read,Show)
instance Eq a => Eq (Rel a) where
 (R []) == (R []) = True
 (R (x:xs)) == (R ys) = any (==x) ys && (R xs) == (R (quitar x ys))

-- Funcion auxiliar para la instancia de Eq
quitar :: Eq a => a -> [a] -> [a]
quitar x (y:ys) = if x == y then ys else [y] ++ quitar x ys

--esRelacion
esRelacion :: Eq a => Rel a -> Bool
esRelacion (R []) = True
esRelacion (R (x:xs)) = all (/=x) xs && esRelacion (R xs)

--dominio
dominio :: Eq a => Rel a -> [a]
dominio (R xs) = if esRelacion (R xs) then dominioAux (R xs) [] else []

dominioAux :: Eq a => Rel a -> [a] -> [a]
dominioAux (R []) ys = ys
dominioAux (R (x:xs)) ys = if all (/=(fst x)) ys then dominioAux (R xs) (ys++[fst x]) else dominioAux (R xs) ys

--soporte
soporte :: Eq a => Rel a -> [a]
soporte r = if esRelacion r then soporteAux r (dominioAux r []) else []

soporteAux :: Eq a => Rel a -> [a] -> [a]
soporteAux (R []) ys = ys
soporteAux (R (x:xs)) ys = if all (/=(snd x)) ys then soporteAux (R xs) (ys++[snd x]) else soporteAux (R xs) ys

--relEquivalencia
relEquivalencia :: Eq a => Rel a -> Bool
relEquivalencia (R xs) =
 if esRelacion (R xs) 
 then reflexiva (R xs) cjto && simetrica (R xs) xs && transitiva (R xs) xs
 else False
 where cjto = soporteAux (R xs) (dominioAux (R xs) [])

reflexiva :: Eq a => Rel a -> [a] -> Bool
reflexiva (R xs) [] = True
reflexiva (R xs) (y:ys) = any (\x->fst x == y && snd x == y) xs && reflexiva (R xs) ys

simetrica :: Eq a => Rel a -> [(a, a)] -> Bool
simetrica (R []) ys = True
simetrica (R (x:xs)) ys = 
 if fst x /= snd x 
 then any (\y->fst y == snd x && snd y == fst x) ys && simetrica (R xs) ys
 else True && simetrica (R xs) ys

transitiva :: Eq a => Rel a -> [(a, a)] -> Bool
transitiva (R xs) [] = True
transitiva (R xs) (y:ys) = transitivaAux (R xs) (fst y) (filter (\x-> fst x == snd y) xs) && transitiva (R xs) ys

transitivaAux :: Eq a => Rel a -> a -> [(a, a)] -> Bool
transitivaAux (R xs) y [] = True
transitivaAux (R xs) y (z:zs) = any (==(y,snd z)) xs && transitivaAux (R xs) y zs

--conjCociente
--conjCociente r

--generaDiv
generaDiv :: Integral a => a -> a -> Rel a
generaDiv n m = (R [(x,y) | y <- [0..m], x <- [n..m], mod y x == 0])

--generaGE
generaGE :: Ord a => [a] -> Rel a
generaGE xs = (R (generaGEAux xs))

generaGEAux :: Ord a => [a] -> [(a, a)]
generaGEAux [] = []
generaGEAux (x:xs) =
 [(x,x)] ++ generaGEAux1 x (filter (\y-> y <= x) xs) ++ generaGEAux2 x (filter (\y-> y > x) xs) ++ generaGEAux xs

generaGEAux1 :: a -> [a] -> [(a, a)]
generaGEAux1 x [] = []
generaGEAux1 x (y:ys) = [(x,y)] ++ generaGEAux1 x ys

generaGEAux2 :: a -> [a] -> [(a, a)]
generaGEAux2 x [] = []
generaGEAux2 x (y:ys) = [(y,x)] ++ generaGEAux2 x ys


--composicion
composicion :: Ord a => Rel a -> Rel a -> Rel a
composicion r1 r2 = if (quicksort (soporte r1)) == (quicksort (soporte r2)) && esRelacion r1 && esRelacion r2 then (R (composicionAux r1 r2)) else (R [])

--funcion auxiliar para la comparacion dentro de composicion
quicksort :: Ord a => [a] -> [a]
quicksort [] = []  
quicksort (x:xs) = quicksort [a | a <- xs, a <= x] ++ [x] ++ quicksort [a | a <- xs, a > x]   

composicionAux :: Eq a => Rel a -> Rel a -> [(a, a)]
composicionAux (R []) (R ys) = []
composicionAux (R (x:xs)) (R ys) = composicionAux1 x (filter (\y-> fst y == snd x) ys) ++ composicionAux (R xs) (R ys)

composicionAux1 :: (a, a) -> [(a, a)] -> [(a, a)]
composicionAux1 x [] = []
composicionAux1 x (y:ys) = [(fst x, snd y)] ++ composicionAux1 x ys


--introRel
-- introRel = do
 -- putStrLn "Introduzca los pares de la relacion uno a uno (Char,Char) (('$',Char) para acabar):"
 -- introTup
 -- rel0 <- (R (aux))
 -- return ()
 
-- aux = []
-- introTup = do
 -- l <- getLine
 -- t <- return (read l::(Char,Char))
 -- if (fst t) == '$' then return() else f
 -- where f = do
        -- aux <- return (aux ++ [t])
        -- introTup
      
 