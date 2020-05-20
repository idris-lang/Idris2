module Utils.Either

export
mapError : (a -> c) -> Either a b -> Either c b
mapError f e = either (Left . f) (Right . id) e
