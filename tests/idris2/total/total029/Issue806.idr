module Issue806

total
nonProductive : Integer -> Inf Void
nonProductive x = Delay (nonProductive x)
