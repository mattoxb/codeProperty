fact :: Integer->Integer
fact 0=1
fact 1=1
fact x= x * (fact (x-1))
