module Haskellium where
    import Shape
    import Point

    data Haskellium = Haskellium {
                                    name       :: String,
                                    lastName1  :: String,
                                    lastName2  :: String,
                                    location   :: Point,
                                    houseShape :: Shape
    } deriving (Show, Eq)

    son :: Haskellium -> Haskellium -> String -> Haskellium
    son haskelliumA haskelliumB named = Haskellium {
                                    name = named,
                                    lastName1 = lastName1 haskelliumA,
                                    lastName2 = lastName1 haskelliumB,
                                    location = location haskelliumA,
                                    houseShape = houseShape haskelliumA
    }

    houseCost :: Haskellium -> Float
    houseCost haskellium = (perimeter (houseShape haskellium) * 2.5) + area (houseShape haskellium) * 2

    timeToWork :: Haskellium -> Float
    timeToWork haskellium =
        if fromO (location haskellium) < 300
            then fromO (location haskellium) / 30
        else fromO (location haskellium) / 70
        