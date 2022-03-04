factk :: Integer -> (Integer -> t) -> t
factk 0 k = k 1
factk n k = factk (n-1) (\v -> k (n * v))
