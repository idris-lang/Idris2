-- TODO: retire after release 0.6
module Libraries.Data.These

import Data.These

%default total

public export
fromMaybes : Maybe a -> Maybe b -> Maybe (These a b)
fromMaybes (Just a) mb = pure $ maybe (This a) (Both a) mb
fromMaybes ma (Just b) = pure $ maybe (That b) (flip Both b) ma
fromMaybes Nothing Nothing = Nothing
