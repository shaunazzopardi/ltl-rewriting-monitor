module LTL(rewrite) where
    
    import Data.List
    import Data.Maybe

    data LTL 
        = T
        | F
        | Event Int
        | Or LTL LTL
        | And LTL LTL
        | Not LTL
        | Until LTL LTL
        | Next LTL
        deriving(Eq, Show)

    rewrite :: LTL -> [Int] -> LTL
    rewrite T is = T
    rewrite F is = F
    rewrite (Event i) is = if elem i is
                            then T
                            else F

    rewrite (Or pi pi') is 
        = if rpi == T || rpi' == T
            then T
            else if rpi == F && rpi' == F
                then F
                else reduce (Or rpi rpi')
        where 
            rpi = rewrite pi is
            rpi' = rewrite pi' is

    rewrite (And pi pi') is 
        = if rpi == T && rpi' == T
            then T
            else if rpi == F || rpi' == F
                then F
                else reduce (And rpi rpi')
        where 
            rpi = rewrite pi is
            rpi' = rewrite pi' is

    rewrite (Not pi) is
        = if rpi == T
            then F
            else if rpi == F
                    then T
                    else Not rpi
        where
            rpi = rewrite pi is
            
    rewrite (Until pi pi') is 
        = if rpi == F
            then rpi'
            else reduce (Or ((Until pi pi')) (rpi'))
        where 
            rpi = rewrite pi is
            rpi' = rewrite pi' is

    reduce :: LTL -> LTL
    reduce(And T pi) = pi
    reduce(And pi T) = pi
    reduce(And _ F) = F
    reduce(And F _) = F
    reduce(Or _ T) = T
    reduce(Or T _) = T
    reduce(Or pi F) = pi
    reduce(Or F pi) = pi
    reduce(pi) = pi
