factk :: Integer -> (a -> Integer)
factk 0 = \_ -> 1
factk n = let f1 = factk (n-1) in \_ -> f1 () * n
