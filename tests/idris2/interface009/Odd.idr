interface Foo m where
  bar : k -> v -> m k v -> m k v

-- This is kind of meaningless, except it exposes a potential error where
-- (\s, t => List (s, t)) is substituted in as 'm' in 'm k v' and the ks
-- clash, so one has to be renamed.
Eq k => Foo (\s, t => List (s, t)) where
  bar x y z = ?bang
